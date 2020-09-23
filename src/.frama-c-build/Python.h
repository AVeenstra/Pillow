// From Python.h:
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

// Disable checks:
#define HAVE_PROTOTYPES
#define STDC_HEADERS
#define SIZEOF_INT 4

// Define types:
typedef size_t Py_ssize_t;
typedef struct _object {
    Py_ssize_t ob_refcnt;
    struct _typeobject *ob_type;
} PyObject;

