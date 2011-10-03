/* This file is automatically generated with "make proto". DO NOT EDIT */

int allow_access(char *addr, char *host, char *allow_list, char *deny_list);
char *auth_server(int fd, int module, char *addr, char *leader);
void auth_client(int fd, char *user, char *challenge);
int make_backup(char *fname);
void write_batch_flist_file(char *buff, int bytes_to_write);
void write_batch_flist_info(int flist_count, struct file_struct **fptr);
void write_char_bufs(char *buf);
void write_batch_argvs_file(int argc, char *argv[]);
struct file_list *create_flist_from_batch(void);
int read_batch_flist_file(char *buff, int len);
unsigned char read_batch_flags();
void read_batch_flist_info(struct file_struct **fptr);
void write_batch_csums_file(void *buff, int bytes_to_write);
void close_batch_csums_file(void);
void write_batch_csum_info(int *flist_entry, int flist_count,
			   struct sum_struct *s);
int read_batch_csums_file(char *buff, int len);
void read_batch_csum_info(int flist_entry, struct sum_struct *s,
			  int *checksums_match);
void write_batch_delta_file(char *buff, int bytes_to_write);
void close_batch_delta_file(void);
int read_batch_delta_file(char *buff, int len);
void show_flist(int index, struct file_struct **fptr);
void show_argvs(int argc, char *argv[]);
uint32 get_checksum1(char *buf1,int len);
void get_checksum2(char *buf,int len,char *sum);
void file_checksum(char *fname,char *sum,OFF_T size);
void checksum_init(void);
void sum_init(void);
void sum_update(char *p, int len);
void sum_end(char *sum);
void _exit_cleanup(int code, const char *file, int line);
void cleanup_disable(void);
void cleanup_set(char *fnametmp, char *fname, struct file_struct *file,
		 struct map_struct *buf, int fd1, int fd2);
void cleanup_set_pid(int pid);
char *client_addr(int fd);
char *client_name(int fd);
void client_sockaddr(int fd,
		     struct sockaddr_storage *ss,
		     socklen_t *ss_len);
int lookup_name(int fd, const struct sockaddr_storage *ss,
		socklen_t ss_len,
		char *name_buf, size_t name_buf_len,
		char *port_buf, size_t port_buf_len);
int compare_addrinfo_sockaddr(const struct addrinfo *ai,
			      const struct sockaddr_storage *ss);
int check_name(int fd,
	       const struct sockaddr_storage *ss,
	       char *name_buf);
int start_socket_client(char *host, char *path, int argc, char *argv[]);
int daemon_main(void);
void setup_protocol(int f_out,int f_in);
int claim_connection(char *fname,int max_connections);
int check_exclude(char *name, struct exclude_struct **local_exclude_list,
		  STRUCT_STAT *st);
void add_exclude_list(const char *pattern, struct exclude_struct ***list, int include);
void add_exclude(const char *pattern, int include);
struct exclude_struct **make_exclude_list(const char *fname,
					  struct exclude_struct **list1,
					  int fatal, int include);
void add_exclude_file(const char *fname, int fatal, int include);
void send_exclude_list(int f);
void recv_exclude_list(int f);
char *get_exclude_tok(char *p);
void add_exclude_line(char *p);
void add_include_line(char *p);
void add_cvs_excludes(void);
int sparse_end(int f);
int write_file(int f,char *buf,size_t len);
struct map_struct *map_file(int fd,OFF_T len);
char *map_ptr(struct map_struct *map,OFF_T offset,int len);
void unmap_file(struct map_struct *map);
void show_flist_stats(void);
int readlink_stat(const char *path, STRUCT_STAT * buffer, char *linkbuf);
int link_stat(const char *path, STRUCT_STAT * buffer);
struct file_struct *make_file(int f, char *fname, struct string_area **ap,
			      int noexcludes);
void send_file_name(int f, struct file_list *flist, char *fname,
		    int recursive, unsigned base_flags);
struct file_list *send_file_list(int f, int argc, char *argv[]);
struct file_list *recv_file_list(int f);
int file_compare(struct file_struct **f1, struct file_struct **f2);
int flist_find(struct file_list *flist, struct file_struct *f);
void free_file(struct file_struct *file);
struct file_list *flist_new();
void flist_free(struct file_list *flist);
char *f_name(struct file_struct *f);
int recv_generator(char *fname, struct file_list *flist, int i, int f_out);
void generate_files(int f,struct file_list *flist,char *local_name,int f_recv);
int main(int argc, char *argv[]);
void init_hard_links(struct file_list *flist);
int check_hard_link(struct file_struct *file);
void do_hard_links(void);
void init_add_list(struct add_list * add_list);
void buffer_add(struct add_list * add_list,OFF_T offset, int length) ;
void buffer_copy(struct copy_graph_node ** copy_graph_head, 
	    int block, OFF_T target, int length);
struct copy_graph_node * permute_copies( 
	struct copy_graph_node **copy_graph_head, struct add_list * add_list);
void send_inplace_data(int f_out,struct map_struct * buf,
		    struct copy_graph_node *copy_graph_head,
		struct add_list * add_list);
void io_set_error_fd(int fd);
int32 read_int(int f);
int64 read_longint(int f);
void read_buf(int f,char *buf,size_t len);
void read_sbuf(int f,char *buf,size_t len);
unsigned char read_byte(int f);
void io_start_buffering(int fd);
void io_flush(void);
void io_end_buffering(void);
void write_int(int f,int32 x);
void write_int_named(int f, int32 x, const char *phase);
void write_longint(int f, int64 x);
void write_buf(int f,char *buf,size_t len);
void write_byte(int f,unsigned char c);
int read_line(int f, char *buf, size_t maxlen);
void io_printf(int fd, const char *format, ...);
void io_start_multiplex_out(int fd);
void io_start_multiplex_in(int fd);
int io_multiplex_write(enum logcode code, char *buf, size_t len);
void io_multiplexing_close(void);
char *lp_motd_file(void);
char *lp_log_file(void);
char *lp_pid_file(void);
char *lp_socket_options(void);
int lp_syslog_facility(void);
char *lp_name(int );
char *lp_comment(int );
char *lp_path(int );
char *lp_lock_file(int );
BOOL lp_read_only(int );
BOOL lp_list(int );
BOOL lp_use_chroot(int );
BOOL lp_transfer_logging(int );
BOOL lp_ignore_errors(int );
BOOL lp_ignore_nonreadable(int );
char *lp_uid(int );
char *lp_gid(int );
char *lp_hosts_allow(int );
char *lp_hosts_deny(int );
char *lp_auth_users(int );
char *lp_secrets_file(int );
BOOL lp_strict_modes(int );
char *lp_exclude(int );
char *lp_exclude_from(int );
char *lp_include(int );
char *lp_include_from(int );
char *lp_log_format(int );
char *lp_refuse_options(int );
char *lp_dont_compress(int );
int lp_timeout(int );
int lp_max_connections(int );
BOOL lp_load(char *pszFname, int globals_only);
int lp_numservices(void);
int lp_number(char *name);
void err_list_push(void);
void log_init(void);
void log_open();
void log_close();
void set_error_fd(int fd);
void rwrite(enum logcode code, char *buf, int len);
void rprintf(enum logcode code, const char *format, ...);
void rsyserr(enum logcode code, int errcode, const char *format, ...);
void rflush(enum logcode code);
void log_send(struct file_struct *file, struct stats *initial_stats);
void log_recv(struct file_struct *file, struct stats *initial_stats);
void log_exit(int code, const char *file, int line);
void log_transfer(struct file_struct *file, const char *fname);
void wait_process(pid_t pid, int *status);
int child_main(int argc, char *argv[]);
void start_server(int f_in, int f_out, int argc, char *argv[]);
int client_run(int f_in, int f_out, pid_t pid, int argc, char *argv[]);
int main(int argc,char *argv[]);
void match_sums(int f, struct sum_struct *s, struct map_struct *buf, OFF_T len);
void match_report(void);
void usage(enum logcode F);
void option_error(void);
int parse_arguments(int *argc, const char ***argv, int frommain);
void server_options(char **args,int *argc);
BOOL pm_process( char *FileName,
                 BOOL (*sfunc)(char *),
                 BOOL (*pfunc)(char *, char *) );
pid_t piped_child(char **command, int *f_in, int *f_out);
pid_t local_child(int argc, char **argv,int *f_in,int *f_out,
		  int (*child_main)(int, char*[]));
void end_progress(OFF_T size);
void show_progress(OFF_T ofs, OFF_T size);
void delete_files(struct file_list *flist);
int recv_files(int f_in,struct file_list *flist,char *local_name,int f_gen);
void free_sums(struct sum_struct *s);
int delete_file(char *fname);
int set_perms(char *fname,struct file_struct *file,STRUCT_STAT *st,
	  int report);
void sig_int(void);
void finish_transfer(char *fname, char *fnametmp, struct file_struct *file);
void send_files(struct file_list *flist,int f_out,int f_in);
int try_bind_local(int s,
		   int ai_family, int ai_socktype,
		   const char *bind_address);
int open_socket_out(char *host, int port, const char *bind_address,
		    int af_hint);
int open_socket_out_wrapped (char *host,
			     int port,
			     const char *bind_address,
			     int af_hint);
int is_a_socket(int fd);
void start_accept_loop(int port, int (*fn)(int ));
void set_socket_options(int fd, char *options);
void become_daemon(void);
int sock_exec(const char *prog);
int do_unlink(char *fname);
int do_symlink(char *fname1, char *fname2);
int do_link(char *fname1, char *fname2);
int do_lchown(const char *path, uid_t owner, gid_t group);
int do_mknod(char *pathname, mode_t mode, dev_t dev);
int do_rmdir(char *pathname);
int do_open(char *pathname, int flags, mode_t mode);
int do_chmod(const char *path, mode_t mode);
int do_rename(char *fname1, char *fname2);
void trim_trailing_slashes(char *name);
int do_mkdir(char *fname, mode_t mode);
int do_mkstemp(char *template, mode_t perms);
int do_stat(const char *fname, STRUCT_STAT *st);
int do_lstat(const char *fname, STRUCT_STAT *st);
int do_fstat(int fd, STRUCT_STAT *st);
OFF_T do_lseek(int fd, OFF_T offset, int whence);
void *do_mmap(void *start, int len, int prot, int flags, int fd, OFF_T offset);
char *d_name(struct dirent *di);
int main(int argc, char **argv);
int main (int argc, char *argv[]);
void set_compression(char *fname);
void send_token(int f,int token,struct map_struct *buf,OFF_T offset,
		int n,int toklen);
int recv_token(int f,OFF_T * offset,char **data);
void see_token(char *data, int toklen);
int main(int argc, char **argv);
void add_uid(uid_t uid);
void add_gid(gid_t gid);
void send_uid_list(int f);
void recv_uid_list(int f, struct file_list *flist);
void set_nonblocking(int fd);
void set_blocking(int fd);
int fd_pair(int fd[2]);
void print_child_argv(char **cmd);
void out_of_memory(char *str);
void overflow(char *str);
int set_modtime(char *fname, time_t modtime);
int create_directory_path(char *fname, int base_umask);
int copy_file(char *source, char *dest, mode_t mode);
int robust_unlink(char *fname);
int robust_rename(char *from, char *to);
pid_t do_fork(void);
void kill_all(int sig);
int name_to_uid(char *name, uid_t *uid);
int name_to_gid(char *name, gid_t *gid);
int lock_range(int fd, int offset, int len);
void glob_expand(char *base1, char **argv, int *argc, int maxargs);
void strlower(char *s);
void *Realloc(void *p, int size);
void clean_fname(char *name);
void sanitize_path(char *p, char *reldir);
char *push_dir(char *dir, int save);
int pop_dir(char *dir);
int u_strcmp(const char *cs1, const char *cs2);
int unsafe_symlink(char *dest, char *src);
char *timestring(time_t t);
int msleep(int t);
int cmp_modtime(time_t file1, time_t file2);
char *  timing(int end);
int _Insure_trap_error(int a1, int a2, int a3, int a4, int a5, int a6);
int sys_gettimeofday(struct timeval *tv);
