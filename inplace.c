/* 
   Copyright (C) Andrew Tridgell 1996
   Copyright (C) Paul Mackerras 1996
   
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   This file, inplace.c, Copyright (C) David Rasch 2002

   $Id: inplace.c,v 1.32 2003/03/18 01:24:59 rasch Exp $

   $Date: 2003/03/18 01:24:59 $
   $Source: /home/rasch/cvsroot/rsync2/src/inplace.c,v $
   $Revision: 1.32 $
*/
#include "rsync.h"

extern int inplace;
extern int do_stats;

static int extra_memory;
static int max_extra_memory;
static int extra_bytes;
static int broken_copies;
static int cycles_broken;
static int bytes_trimmed;
extern struct stats stats;

static void update_extra_memory(int delta){
    extra_memory += delta;
    if(extra_memory > stats.extra_memory){
        stats.extra_memory = extra_memory;
    }
    if(extra_memory > max_extra_memory){
        max_extra_memory = extra_memory;
    }
}


/**
 * itialize an already allocated add_list
 */
void init_add_list(struct add_list * add_list)
{
    add_list->head = NULL;
    add_list->tail = NULL;
    extra_memory = 0;
    extra_bytes = 0;
    max_extra_memory = 0;
    broken_copies = 0;
    bytes_trimmed = 0;
    cycles_broken = 0;
}

/**
 * place an add command on the end of the list 
 */
void buffer_add(struct add_list * add_list,OFF_T offset, int length) 
{
    struct add_list_node * newadd;

    if(verbose > 3){
        rprintf(FINFO, "Buffering add: offset=%.0f length=%d\n",
                (double) offset, length);
    }
    newadd = (struct add_list_node *) 
        malloc(sizeof(struct add_list_node));
    update_extra_memory(sizeof(struct add_list_node));
    if(add_list->head==NULL){
        add_list->head = newadd;
    }
    else {
        add_list->tail->next = newadd;
    }
    newadd->next = NULL;
    add_list->tail = newadd;
    newadd->add.offset = offset;
    newadd->add.length = length;

}

/**
 * place a copy command in the node list for the copy_graph
 */
void buffer_copy(struct copy_graph_node ** copy_graph_head, 
            int block, OFF_T target, int length)
{
    struct copy_graph_node * newcopy;
    if(verbose > 3){
        rprintf(FINFO, "Buffering copy: block=%d offset=%.0f length=%d\n",
                block, (double) target, length);
    }
    newcopy = (struct copy_graph_node *) 
        malloc(sizeof(struct copy_graph_node));
    
    update_extra_memory(sizeof(struct copy_graph_node));

    newcopy->next = *copy_graph_head;
    newcopy->visited = UNVISITED;
    newcopy->references = 0;
    newcopy->edge = NULL;
    *copy_graph_head = newcopy;

    switch(inplace){
        case 1:
            newcopy->u.copy = 
                (struct copy *) malloc(sizeof(struct copy));
            update_extra_memory(sizeof(struct copy));
            newcopy->u.copy->target = target;
            newcopy->u.copy->block = block;
            newcopy->u.copy->length = length;
            break;

        case 2:
            newcopy->u.copy_trim = 
                (struct copy_trim *) 
                    malloc(sizeof(struct copy_trim));
            update_extra_memory(sizeof(struct copy_trim));
            newcopy->u.copy_trim->target = target;
            newcopy->u.copy_trim->block = block;
            newcopy->u.copy_trim->length = length;
            newcopy->u.copy_trim->b_offset = 0;
            newcopy->u.copy_trim->e_offset = length;
            break;
    }
}

/**
 * compare two nodes, tells in which order they should be sorted based on their
 * destination offset
 */
static int node_compare(const void * a, const void * b){
    if(((struct copy_graph_node *)a)->u.copy->target < ((struct
                    copy_graph_node*)b)->u.copy->target ){
        return -1;
    }
    else if(((struct copy_graph_node *)a)->u.copy->target == ((struct
                    copy_graph_node*)b)->u.copy->target ){
        return 0;
    }
    else return 1;
}

/**
 * determine the weight of an edge between source/dest.  This edge doesn't need
 * to exist
 */
static int edge_weight(struct copy_graph_node * source, 
                        struct copy_graph_node * dest){
    if (source==dest ){
        return 0;
    }
    else { 
        OFF_T s_start = source->u.copy->block * BLOCK_SIZE;
        OFF_T s_end = s_start + source->u.copy->length;
        OFF_T d_start = dest->u.copy->target;
        OFF_T d_end = d_start + dest->u.copy->length;
        
        int weight;
        

        if(inplace == 2 ) {
            s_end = s_start+source->u.copy_trim->e_offset;
            s_start = s_start+source->u.copy_trim->b_offset;
        }

        weight = MIN(s_end,d_end)-MAX(s_start,d_start);
        if(verbose>3){
            if(inplace == 1){
                rprintf(FINFO,"Evaluating edge weight, read_block=%d "
                        "length=%d write=%.0f weight=%d\n", source->u.copy->block,
                        source->u.copy->length,(double)dest->u.copy->target,
                        weight);
            }
            else {
                rprintf(FINFO,"Evaluating edge weight, read_block=%d+%d-%d "
                        "length=%d write=%.0f weight=%d\n", source->u.copy->block,
                        source->u.copy_trim->b_offset,source->u.copy_trim->e_offset,
                        source->u.copy->length,(double)dest->u.copy->target,
                        weight);

            }
        }
        
        return (weight<0)?0:weight;
    }
}

/**
 * find all edges originating from one node and create edge structures in the
 * graph so that the DFS can find a legal ordering
 */
static void probe_edges(int i, struct copy_graph_node ** search_array,
            int count){

    /* binary search */
    int position = count/2; 
    int next_jump = count/4; 


    OFF_T source = search_array[i]->u.copy->block*BLOCK_SIZE;
    
    if(search_array[i]->u.copy->target > source){
        broken_copies++;
    }


    while(0<= position && position < count && next_jump!=0){
        if(verbose>4){
            rprintf(FINFO, "Binary Search pos=%d jump=%d\n",position,next_jump);
        }
        if(search_array[position]->u.copy->target< source){ /* go right */
            position += next_jump;
            next_jump /= 2;
        } else if(search_array[position]->u.copy->target > source){ /* go left*/
            position -= next_jump; 
            next_jump /= 2;
        } else {
            break;      
        }
    }
    if(verbose>4){
        rprintf(FINFO, "binary search done pos=%d\n",position);
    }
    /* either moved to right part of the array, or found an exact match for
     * source/target.  Move iterator k to the left until we find no conflict */

    while(position>=0 && (edge_weight(search_array[i],search_array[position])
                || position==i)) {
        position--;
    }
    position++;

    while(position<count &&
            (edge_weight(search_array[i],search_array[position]) ||
             position==i)){
        if(position!=i) {
            struct copy_graph_edge * edge; 
            edge = (struct copy_graph_edge *)malloc(sizeof(struct copy_graph_edge));
            update_extra_memory(sizeof(struct copy_graph_edge));
            edge->dest = search_array[position];
            edge->dest->references++;
            edge->next = search_array[i]->edge;
            search_array[i]->edge = edge;
        }
        position++;
    }
}

/**
 *  Build edges for the whole copy graph based on dependencies among copies
 */
static struct copy_graph_node ** build_edges(struct copy_graph_node *
        copy_graph_head,int *count)
{
    int i=0;
    struct copy_graph_node * curnode;
    struct copy_graph_node ** search_node;

    for(curnode = copy_graph_head;curnode!= NULL;curnode=curnode->next){
        i++;
    }
    *count = i;

    search_node= (struct copy_graph_node **) calloc(*count,sizeof(struct
                copy_graph_node *));
    update_extra_memory(*count  * sizeof(struct copy_graph_node * ));
    if(verbose>3){
        rprintf(FINFO, "Built array of size %d for qsort\n",sizeof(struct
                copy_graph_node *)*(*count));
    }
    /*copy linked list to array for qsort*/
    for(i=0,curnode = copy_graph_head;curnode!=NULL;i++,curnode=curnode->next){
        search_node[i]= curnode;        
    }

    if(verbose>3)
    {
        rprintf(FINFO, "Starting qsort\n");
    }
    qsort(search_node,*count,sizeof(struct copy_graph_node *),node_compare);

    if(verbose>3)
    {
        rprintf(FINFO, "Starting edge detection\n");
    }
    /* now probe with each node for its edges */
    for(i=0;i<*count;i++){
        if(verbose >4){
            rprintf(FINFO, "Probing for edges %d/%d\n",i,*count);
        }
        probe_edges(i,search_node,*count);
    }
    if(verbose>3)
    {
        rprintf(FINFO, "Done edge detection\n");
    }
    //free(search_node);
    return search_node;
}


/**
 * shrink a node for inplace==2.  This shrinks a node rather than deleting it
 * in order to make the edge_weight 0
 */
static void shrink_node(struct copy_graph_node * src,
                        struct copy_graph_node * dest){
    OFF_T start = src->u.copy_trim->block * BLOCK_SIZE +
        src->u.copy_trim->b_offset;
    OFF_T end = src->u.copy_trim->block * BLOCK_SIZE +
        src->u.copy_trim->e_offset;

    if(verbose>3){
        rprintf(FINFO,"Shrinking: src (read) start=%.0f "
                "end=%.0f\n",(double)start,(double)end);
    }   
    if(verbose>3){
        rprintf(FINFO,"Shrinking: dest (write) start=%.0f "
                "end=%.0f\n",(double)dest->u.copy_trim->target,
                (double)dest->u.copy_trim->target+dest->u.copy_trim->length);
    }
    
    /* start needs trimmed */
    if(start < (dest->u.copy_trim->target + dest->u.copy_trim->length ) 
            && (dest->u.copy_trim->target <= start)){
        unsigned int trim =
            dest->u.copy_trim->target+dest->u.copy_trim->length-start;
        src->u.copy_trim->b_offset = trim;
        bytes_trimmed += trim;
        if(verbose>3){
            rprintf(FINFO, "Trimming leading edge by %d bytes\n",trim);
        }
    }
    /* end needs trimmed */
    if(dest->u.copy_trim->target <= end
            && end < (dest->u.copy_trim->target+dest->u.copy_trim->length)){
        unsigned int trim = end - dest->u.copy_trim->target;
        src->u.copy_trim->e_offset = src->u.copy_trim->length-trim;
        bytes_trimmed += trim;
        if(verbose>3){
            rprintf(FINFO, "Trimming tail edge by %d bytes\n",trim);
        }
    }

    if(src->u.copy_trim->e_offset <= src->u.copy_trim->b_offset){
        src->u.copy_trim->b_offset = 0;
        src->u.copy_trim->e_offset = 0;
    }

}

/**
 * perform the topological sorting on the graph.  Returned is the head to a
 * topologically sorted list of nodes
 */
static struct copy_graph_node * topo_sort(
                                        struct copy_graph_node ** node_array,
                                        int count,
                                        struct add_list * add_list){
    int j;
    struct copy_graph_node * topo_head = NULL; 
    struct copy_stack * copy_top = NULL;

    for(j=count-1;j>=0;j--){
        struct copy_graph_node * bottom_node;
        bottom_node = node_array[j];
        if(bottom_node->visited == FINISHED
                || bottom_node->visited == DELETED){
            continue;
        }
        bottom_node->next = NULL;
        copy_top = (struct copy_stack * ) malloc(sizeof(struct copy_stack)); 
        update_extra_memory(sizeof(struct copy_stack));
        copy_top->below = NULL;
        copy_top->data = bottom_node;
        copy_top->data->visited = ON_STACK;


        while(copy_top != NULL){
            struct copy_graph_node * current_node = copy_top->data;
            struct copy_graph_edge * current_edge = copy_top->data->edge;
            if(verbose >3){
                rprintf(FINFO, "looking at node src=%d target=%.0f\n",
                        copy_top->data->u.copy->block,
                        (double)copy_top->data->u.copy->target);
            }

            if(!current_edge){
                struct copy_stack * temp_copy_top;
                /* pop node off and put it on the front of the topo list*/
                current_node->visited = FINISHED;

                /* put on topo list as finished (if not deleted)*/
        //      rprintf(FINFO,"Putting on to topo list: %08x\n",current_node);
                current_node->next = topo_head;
                topo_head = current_node;

                /* pop off stack */
                temp_copy_top = copy_top->below;
                update_extra_memory(-sizeof(struct copy_stack));
                free(copy_top);
                copy_top = temp_copy_top;       
                
                
                if(verbose >4){
                    rprintf(FINFO, "finished node\n");
                }
            }
            else {
                /* remove edge from list */
                copy_top->data->edge = current_edge->next;
                current_edge->dest->references--;

                /* is its target already on stack? */
                if(current_edge->dest->visited == ON_STACK){
                    /* resolve cycle */
                    stats.broken_cycles++;
                    cycles_broken++;
                    if(inplace==1){
                        current_edge->dest->visited = DELETED;
                        buffer_add(add_list,current_edge->dest->u.copy->target,
                                current_edge->dest->u.copy->length);
                        if(verbose >3 ){
                            rprintf(FINFO,"Deleting copy src=%.0f len=%d\n",
                                            (double)current_edge->dest->u.copy->target,
                                            current_edge->dest->u.copy->length);
                        }
                    }
                    else if(inplace==2){
                        struct copy_graph_node * best_src_node = current_node;
                        struct copy_graph_node * best_dest_node = current_edge->dest;
                        int min_edge_weight = edge_weight(best_src_node,best_dest_node);
                        struct copy_stack * current_stack_node = copy_top;

                        current_stack_node = copy_top;
                        /* iterate down through stack and find best edge to trim*/
                        while(current_stack_node->data != current_node){
                            int temp_weight =
                                edge_weight(current_stack_node->below->data,
                                            current_stack_node->data);
                            if(temp_weight < min_edge_weight){
                                best_src_node = current_stack_node->below->data;
                                best_dest_node = current_stack_node->data;
                                min_edge_weight = temp_weight;
                            }
                        }
                        
                        /* restore stack to appropriate position */
                        current_stack_node = copy_top;
                        do {
                            struct copy_stack * temp_stack_node;
                            /*rprintf(FINFO,"Current_stack_node: %.8x data:%.8x\n",
                                        current_stack_node,
                                        current_stack_node->data);*/
                            current_stack_node->data->visited = UNVISITED;
                            if (current_stack_node->below 
                                    && current_stack_node->below 
                                        != best_src_node){

                                current_edge = (struct copy_graph_edge *)
                                        malloc(sizeof(struct copy_graph_edge));
                                current_edge->dest = current_stack_node->data;
                                current_edge->next = current_stack_node->below->data->edge;
                                current_stack_node->below->data->edge = current_edge;

                            }
                            temp_stack_node = current_stack_node; 
                            current_stack_node = current_stack_node->below;
                            update_extra_memory(-sizeof(struct copy_stack));
                            free(temp_stack_node);
                        } while(current_stack_node && current_stack_node->data != best_src_node);
                        copy_top = current_stack_node;

                        current_node = NULL;
                        current_edge = NULL;

                        if(copy_top){
                            current_node = copy_top->data;
                            current_edge = copy_top->data->edge;
                        }

                        if(verbose > 3){
                            rprintf(FINFO,"Trimming copy "
                                    "weight=%d\n",edge_weight(best_src_node,best_dest_node));
                        }
                        shrink_node(best_src_node,best_dest_node);
                        if(edge_weight(best_src_node,best_dest_node)>0){
                            rprintf(FINFO, "dependency not fixed\n");
                        }

                    }
                } 
                else if(current_edge->dest->visited == DELETED){

                } 
                else if(current_edge->dest->visited != FINISHED
                        && 0!=edge_weight(current_node,
                                current_edge->dest)) {
                    struct copy_stack * new_copy_top;
                    
                    /* push new node */
                    new_copy_top = (struct copy_stack *)
                        malloc(sizeof(struct copy_stack));
                    update_extra_memory(sizeof(struct copy_stack));
                    new_copy_top->below = copy_top;
                    new_copy_top->data = current_edge->dest;
                    new_copy_top->data->visited = ON_STACK;
                    copy_top = new_copy_top;

                }
                /* free edge */
                if(current_edge){
                    update_extra_memory(-sizeof(struct copy_graph_edge));
                    free(current_edge);
                }
            }
        }
    }
    return topo_head;
}

struct copy_graph_node * permute_copies( 
        struct copy_graph_node **copy_graph_head, struct add_list * add_list)
{
    int count;
    struct copy_graph_node * topo_list_head;
    struct copy_graph_node ** node_array;

    if(do_stats){
        timing(TIMING_START);
    }
    node_array = build_edges(*copy_graph_head,&count);
    if(do_stats){
        rprintf(FINFO, "Build graph: %s\n", timing(TIMING_END));
    }
    if(do_stats){
        timing(TIMING_START);
    }
    topo_list_head = topo_sort(node_array,count, add_list);
    if(do_stats){
        rprintf(FINFO, "Topological sort: %s\n", timing(TIMING_END));
    }
    update_extra_memory(-(count * sizeof(struct copy_graph_node * )));
    if(do_stats){
        rprintf(FINFO, "Extra memory: %d Extra bytes sent: %d\n",
                max_extra_memory,extra_bytes);
        rprintf(FINFO, "Broken copies without delta comp: %d\n",
                broken_copies);
        rprintf(FINFO, "Cycles broken: %d Bytes trimmed: %d\n",
                cycles_broken, bytes_trimmed);
    }

    free(node_array);
    return topo_list_head;
}


void send_inplace_data(int f_out,struct map_struct * buf,
                    struct copy_graph_node *copy_graph_head,
                struct add_list * add_list)
{
    while(copy_graph_head!= NULL){
        struct copy_graph_node * temp_copy_node; 
        //rprintf(FINFO,"Pulling off of topo list: %08x\n",copy_graph_head->u.copy);
        if(copy_graph_head->visited ==DELETED){
            buffer_add(add_list,copy_graph_head->u.copy->block * BLOCK_SIZE,
                    copy_graph_head->u.copy->length);
            extra_bytes += copy_graph_head->u.copy->length;
            stats.total_extra_written += copy_graph_head->u.copy->length;
            continue;
        }
        send_token(f_out,copy_graph_head->u.copy->block,buf,
                copy_graph_head->u.copy->target,0,copy_graph_head->u.copy->length);
        extra_bytes += sizeof(long int);
        if(inplace == 2){
            OFF_T start = copy_graph_head->u.copy_trim->target;
            
            if(copy_graph_head->u.copy_trim->b_offset > 0){
                if(verbose>4){
                    rprintf(FINFO,"sending: start=%.0f "
                        "end=%.0f\n",
                        (double)copy_graph_head->u.copy_trim->target,
                        (double)(copy_graph_head->u.copy_trim->target 
                                +copy_graph_head->u.copy_trim->b_offset));
                }
                //send_token(f_out,-2,buf,start,
                 //       copy_graph_head->u.copy_trim->b_offset,0);
                buffer_add(add_list,start,copy_graph_head->u.copy_trim->b_offset);
                extra_bytes += sizeof(long int);
                extra_bytes += copy_graph_head->u.copy_trim->b_offset;
                stats.total_extra_written += sizeof(long int)+
                    copy_graph_head->u.copy_trim->b_offset;

            }
            if(copy_graph_head->u.copy_trim->e_offset 
                    < copy_graph_head->u.copy_trim->length){
                if(verbose>4){
                    rprintf(FINFO,"sending: start=%.0f "
                        "end=%.0f\n",
                        (double)(start+copy_graph_head->u.copy_trim->e_offset),
                        (double)(copy_graph_head->u.copy_trim->length
                        -copy_graph_head->u.copy_trim->e_offset));
                }
                /*send_token(f_out,-2,buf,start
                        +copy_graph_head->u.copy_trim->e_offset,
                        copy_graph_head->u.copy_trim->length
                        -copy_graph_head->u.copy_trim->e_offset,0);*/
                buffer_add(add_list,start
                        +copy_graph_head->u.copy_trim->e_offset,
                        copy_graph_head->u.copy_trim->length
                        -copy_graph_head->u.copy_trim->e_offset);
                extra_bytes += sizeof(long int);
                extra_bytes += copy_graph_head->u.copy_trim->length -
                                copy_graph_head->u.copy_trim->e_offset;
                stats.total_extra_written +=sizeof(long int) +
                    copy_graph_head->u.copy_trim->length -
                    copy_graph_head->u.copy_trim->e_offset;
            }
        }
        temp_copy_node = copy_graph_head;
        copy_graph_head = copy_graph_head->next;
        update_extra_memory(-((inplace==1)?sizeof(struct copy):sizeof(struct copy_trim)));
        free(temp_copy_node->u.copy);
        update_extra_memory(-sizeof(struct copy_graph_node));
        free(temp_copy_node);
    }

    while(add_list->head != NULL){
        send_token(f_out,-2,buf, 
                add_list->head->add.offset,add_list->head->add.length,0);

        extra_bytes += sizeof(long int);
        stats.total_extra_written += sizeof(long int);

        add_list->tail = add_list->head;
        add_list->head = add_list->head->next;
        update_extra_memory(-sizeof(struct add_list_node));
        free(add_list->tail);
    }
    /* send done */
    send_token(f_out,-1,buf,0,0,0);
    if(do_stats){
        rprintf(FINFO, "Extra bytes sent: %d\n",
                extra_bytes);
    }

}

/**
 * $Log: inplace.c,v $
 * Revision 1.32  2003/03/18 01:24:59  rasch
 * bugs fixed!
 *
 * Revision 1.31  2003/03/16 23:03:13  rasch
 * got -i 1 working i think
 *
 * Revision 1.30  2003/03/16 07:31:54  rasch
 * fixed major bug with offset processing.  got something else wierd going on now
 *
 * Revision 1.29  2003/02/26 04:01:40  rasch
 * doesnt work
 *
 * Revision 1.28  2002/11/21 16:19:03  rasch
 * important change with add buffering
 *
 * Revision 1.27  2002/09/17 15:42:11  rasch
 * change in extra byte reporting
 *
 * Revision 1.26  2002/08/29 01:34:24  rasch
 * bug squashed
 *
 * Revision 1.25  2002/08/10 01:13:51  rasch
 * stats
 *
 * Revision 1.24  2002/08/09 17:34:59  rasch
 * debugging times
 *
 * Revision 1.23  2002/08/04 15:13:36  rasch
 * bug  disapeared?
 *
 * Revision 1.22  2002/08/04 15:09:51  rasch
 * seg fault debugging
 *
 * Revision 1.21  2002/08/01 14:26:41  rasch
 * flushing changes
 *
 * Revision 1.20  2002/08/01 02:35:49  rasch
 * stats compile now
 *
 * Revision 1.19  2002/08/01 02:25:53  rasch
 * added statsistics reporting
 *
 * Revision 1.18  2002/07/31 18:10:16  rasch
 * changes
 *
 * Revision 1.17  2002/07/31 00:14:53  rasch
 * added memory stat
 *
 * Revision 1.16  2002/07/19 17:53:16  rasch
 * full xfer
 *
 * Revision 1.15  2002/07/18 04:56:12  rasch
 * hi
 *
 * Revision 1.14  2002/07/17 15:15:47  rasch
 * added more debugging, fixed bug with tokens and made receiver create non-existent files
 *
 * Revision 1.13  2002/07/17 14:59:57  rasch
 * fix for token sending, as well as a bad linked list error
 *
 * Revision 1.12  2002/07/17 14:48:04  rasch
 * token debugging, plus token send fix in inplace.c
 *
 * Revision 1.11  2002/07/17 14:23:58  rasch
 * some debug changes
 *
 * Revision 1.10  2002/07/17 13:33:36  rasch
 * stupid union fixed
 *
 * Revision 1.9  2002/07/17 13:29:30  rasch
 * rsync.h union change
 *
 * Revision 1.8  2002/07/17 03:52:37  rasch
 * sending of tokens should be done coding
 *
 * Revision 1.7  2002/07/17 03:10:31  rasch
 * fix for edge weight problem
 *
 * Revision 1.6  2002/07/17 03:05:16  rasch
 * graph algorithm done i believe
 *
 * Revision 1.5  2002/07/15 14:54:10  rasch
 * on to graph algorithms
 *
 * Revision 1.4  2002/07/15 14:42:48  rasch
 * receiving end should now support inplace
 *
 * Revision 1.3  2002/07/15 04:09:13  rasch
 * buffering adds
 *
 * Revision 1.2  2002/07/15 03:54:57  rasch
 * utility
 *
 * Revision 1.1  2002/07/15 03:54:24  rasch
 * utility
 *
 */
/* vim: set cindent ts=8 tw=80 softtabstop=4 shiftwidth=4 expandtab: */
