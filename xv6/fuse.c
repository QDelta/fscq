#define FUSE_USE_VERSION 26
#include <fuse.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>

#define FUSE  1

#include "stat.h"
#include "fs.h"

int sys_fstat(const char *path, void *buf);
int sys_read(void *fh, char *buf, size_t sz, off_t off);
int sys_write(char *path, char *buf, size_t sz, off_t off);
void *sys_open(char *path, int omode);
void *sys_create(char *path, int omode);
int sys_fileclose(void *fh);
int sys_readdirent(void *fh, struct dirent *e, off_t off);
int sys_truncate(char *path);

void panic(char *s)
{
  printf("PANIC: %s\n", s);
  exit(-1);
}

static int
fuse_getattr(const char *path, struct stat *stbuf)
{
  struct xv6stat st;
  memset(stbuf, 0, sizeof(struct stat));
  memset(&st, 0, sizeof(struct xv6stat));

  printf("fuse_getattr: %s\n", path);

  int r = sys_fstat(path, (char *) &st);
  printf("sys_fstat: %d %d %d %d\n", r, st.type, st.nlink, st.size);
  if (r >= 0) {
    stbuf->st_mode = (st.type == T_DIR) ? S_IFDIR | 0777 : S_IFREG | 0666;
    stbuf->st_nlink = st.nlink;
    stbuf->st_size = st.size;
  } else {
    r = -ENOENT;
  }
  return r;
}

static int
fuse_open(const char *path, struct fuse_file_info *fi)
{
  printf("fuse_open: %s flags %d\n", path, fi->flags);
  void  *r = sys_open((char *) path, fi->flags);
  fi->fh = (uint64_t) r;
  printf("fuse_open: returns fh %ld\n", fi->fh);
  return (r == 0) ? -1 : 0;
}

static int
fuse_release(const char *path, struct fuse_file_info *fi)
{
  printf("fuse_release: %s fh %ld\n", path, fi->fh);
  int r = sys_fileclose((void *) fi->fh);
  return r;
}

static int
fuse_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
	     off_t offset, struct fuse_file_info *fi)
{
  printf("fuse_readdir: %s\n", path);
  void  *fh = sys_open((char *) path, fi->flags);
  if (fh == 0)
    return -1;
  off_t xv6off = 0;
  struct dirent xv6e;
  int r;
  while ((r = sys_readdirent(fh, &xv6e, xv6off)) > 0) {
    xv6off += sizeof(xv6e);
    if(xv6e.inum == 0)
      continue;
    filler(buf, xv6e.name, NULL, 0);
  }
  (void) sys_fileclose(fh);
  return r;
}

static int
fuse_read(const char *path, char *buf, size_t size, off_t offset,
	  struct fuse_file_info *fi)
{
  printf("fuse_read: %s %ld %ld %ld\n", path, size, offset, fi->fh);
  size = sys_read((char *) fi->fh, buf, size, offset);
  return size;
}

static int
fuse_write(const char *path, const char *buf, size_t size, off_t offset,
	  struct fuse_file_info *fi)
{
  printf("fuse_write: %s %ld %ld %ld\n", path, size, offset, fi->fh);
  size = sys_write((char *) fi->fh, (char *) buf, size, offset);
  return size;
}

static int
fuse_create(const char *path, mode_t m, struct fuse_file_info *fi)
{
    printf("fuse_create: %s %x\n", path, m);
    void *r = sys_open((char *) path, fi->flags);
    fi->fh = (uint64_t) r;
    return (r == 0) ? -1 : 0;
}

static int
fuse_truncate(const char *path, off_t off)
{
    printf("fuse_truncate: %s %ld\n", path, off);
    if (off != 0) return -1;
    return sys_truncate((char *) path);
}

static struct fuse_operations fuse_filesystem_operations = {
  .getattr = fuse_getattr,
  .open    = fuse_open,
  .release = fuse_release,
  .read    = fuse_read,
  .write   = fuse_write,
  .create  = fuse_create,
  .readdir = fuse_readdir,
  .truncate = fuse_truncate,
};

void
cprintf(char *fmt, ...)
{
  va_list argptr;
  va_start(argptr, fmt);
  vprintf(fmt, argptr);
  va_end(argptr);
}

static int fsimg_fd;

void ideinit()
{
  if ((fsimg_fd = open("fs.img", O_RDWR)) < 0) {
    perror("failed to open fs.img");
    exit(-1);
  }
  printf("xv6fs: opened fs.img\n");
}

void
unix_read(int sector, unsigned char *buf, int sz)
{
  ssize_t n = pread(fsimg_fd, buf, sz, sector*512);
  if (n != sz) {
    perror("pread failed\n");
    exit(-1);
  }
}

void
unix_write(int sector, unsigned char *buf, int sz)
{
  ssize_t n = pwrite(fsimg_fd, buf, sz, sector*512);
  if (n != sz) {
    perror("pwrite failed\n");
    exit(-1);
  }
}

void binit();
void fileinit();
void initlog();

int
main(int argc, char **argv)
{
  printf("init xv6\n");
  binit();
  fileinit();
  ideinit();
  initlog();
  printf("init xv6 done\n");
  return fuse_main(argc, argv, &fuse_filesystem_operations, NULL);
}