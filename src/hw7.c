#include "hw7.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>



static matrix_sf *alloc_matrix(char name, unsigned int rows, unsigned int columns) { // Allocate matrix
    matrix_sf *m = malloc(sizeof(matrix_sf) + rows * columns * sizeof(int));
    if (!m) 
        return NULL;
    m->name = name;
    m->num_rows = rows;
    m->num_cols = columns;
    return m;
}

bst_sf* insert_bst_sf(matrix_sf *mat, bst_sf *root) {
    if (!root ) {
        bst_sf *node = malloc(sizeof(bst_sf));
        if (!node) 
            return NULL;
        node->mat = mat;
        node-> right_child = NULL;
        node -> left_child = NULL;
        return node;
    }
    bst_sf *current = root;
    bst_sf *parent = NULL;
    while (current) {
        parent = current;
        if (mat -> name < current->mat->name)
            current = current-> left_child;
        else 
            current = current-> right_child;
    }
    bst_sf *node = malloc(sizeof(bst_sf));
    if (!node) 
        return root;
    node->mat = mat;
    node-> right_child = NULL;
    node -> left_child = NULL;
    if (mat->name < parent->mat->name) 
        parent->left_child = node;
    else 
        parent->right_child = node;
    return root;
}

matrix_sf* find_bst_sf(char name, bst_sf *root) {
    bst_sf *current = root;
    while (current) {
        if (name == current->mat->name) 
            return current->mat;
        if (name < current->mat->name) 
            current = current->left_child;
        else 
            current = current->right_child;
    }
    return NULL;
}

void free_bst_sf(bst_sf *root) {
    if (!root) return;
    free_bst_sf(root->left_child);
    free_bst_sf(root->right_child);
    if (root->mat) 
        free(root->mat);
    free(root);
}

matrix_sf* add_mats_sf(const matrix_sf *mat1, const matrix_sf *mat2) {
    int rows = mat1->num_rows;
    int columns = mat1->num_cols;
    matrix_sf *mat3 = alloc_matrix('?', rows, columns);
    int x = rows*columns;
    for (int i =0; i<x; i++) {
        mat3 -> values[i] = mat1->values[i] + mat2->values[i];
    }
    return mat3;
}

matrix_sf* mult_mats_sf(const matrix_sf *mat1, const matrix_sf *mat2) {
    int rows1 = mat1->num_rows; // rows of mat3
    int columns1 = mat1->num_cols; // same as theoretical rows2
    int columns2 = mat2-> num_cols; // columns of mat3
    matrix_sf *mat3 = alloc_matrix('?', rows1, columns2);
    for (int i =0; i<rows1; i++) {
        for (int j = 0; j<columns2; j++) {
        int sum = 0;
        for (int x = 0; x<columns1; x++) {
            sum += mat1->values[i*columns1 + x] * mat2->values[x*columns2 + j];
        }
        mat3 -> values[i * columns2 + j] = sum;
        }
    }
    return mat3;
}

matrix_sf* transpose_mat_sf(const matrix_sf *mat) {
    int rows = mat->num_rows;
    int columns = mat->num_cols;
    matrix_sf *mat3 = alloc_matrix('?', columns, rows); // Switch cause transpose
    for (int i =0; i<rows; i++) {
        for (int j = 0; j<columns; j++) {
        mat3 -> values[j * rows + i] = mat->values[i * columns + j];
        }
    }
    return mat3;
}

matrix_sf* create_matrix_sf(char name, const char *expr) {
    char *copy = malloc(strlen(expr) + 1);
    strcpy(copy, expr);
    char *string = copy;
    char *endptr;
    long rows = strtol(string, &endptr, 10);
    string = endptr;
    long columns = strtol(string, &endptr, 10);
    string = endptr;
    while (*string != '[')
        string++;
    string++;
    matrix_sf *matrix = alloc_matrix(name, (int)rows, (int)columns);
    int total = (int)rows * (int) columns;
    for (int i = 0; i< total; i++) {
        while (*string == ' ') 
            string++;
        if (*string == ';') {
            string++;
            while (*string == ' ') 
                string++;
        }
        if (*string == ']')
            break;
        matrix->values[i] = (int)strtol(string, &endptr, 10);
        string = endptr;
    }
    free(copy);
    return matrix;
}

char* infix2postfix_sf(char *infix) {
    if (!infix) return NULL;
    int length = strlen(infix);
    char *output = malloc(length + 2);
    int outputi = 0;
    char *stack = malloc(length + 2);
    int top = -1;
    for (int i = 0; i < length; i++) {
        char ch = infix[i];
        if (((char)ch) == ' ') 
            continue;
        if (isupper((unsigned char)ch)) {
            output[outputi++] = ch;
            continue;
        }
        if (ch == '(') {
            stack[++top] = ch;
            continue;
        }
        if (ch == ')') {
            while (top >= 0 && stack[top] != '(') {
                output[outputi++] = stack[top--];
            }
            if (top >= 0 && stack[top] == '(')
                --top;
            continue;
        }
        if (ch == '\'') {
            stack[++top] = ch;
            continue;
        }
        if (ch == '*' || ch == '+') {
            int currentPrecedence;
            if(ch == '*')
                currentPrecedence = 2;
            else 
                currentPrecedence = 1;
            while (top >= 0) {
                char topCh = stack[top];
                if (topCh == '(') 
                    break;
                int topPrecedence;
                if (topCh == '\'') 
                    topPrecedence = 3;
                else if (topCh == '*') 
                    topPrecedence = 2;
                else if (topCh == '+') 
                    topPrecedence = 1;
                else 
                    topPrecedence = 0;
                if (topPrecedence >= currentPrecedence) {
                    output[outputi++] = stack[top--];
                } else 
                    break;
            }
        stack[++top] = ch;
        continue;
        }
    }
    while (top >= 0) 
        output[outputi++] = stack[top--];
    output[outputi] = '\0';
    free(stack);
    return output;
}

matrix_sf* evaluate_expr_sf(char name, char *expr, bst_sf *root) {
    char *postfix = infix2postfix_sf(expr);
    int length = strlen(postfix);
    matrix_sf **stack = malloc((length + 2) * sizeof(matrix_sf*));
    int top = -1;
    for (size_t i = 0; i < length; ++i) {
        char ch = postfix[i];
        if (isupper((char)ch)) {
            matrix_sf *matrix = find_bst_sf(ch, root);
            stack[++top] = matrix;
            continue;
        }
        if (ch == '\'') {
            matrix_sf *matrix = stack[top--];
            matrix_sf *transpose = transpose_mat_sf(matrix);
            if (!transpose) { 
                free(stack); 
                free(postfix); 
                return NULL; 
            }
            transpose->name = '?';
            if (!isalpha(matrix->name)) 
                free(matrix);
            stack[++top] = transpose;
            continue;
        }
        if (ch == '*' || ch == '+') {
            matrix_sf *matrix2 = stack[top--]; // matrix on top
            matrix_sf *matrix1 = stack[top--]; // matrix below it
            matrix_sf *res = NULL;
            if (ch == '*') 
                res = mult_mats_sf(matrix1, matrix2);
            else 
                res = add_mats_sf(matrix1, matrix2);
            if (!res) { 
                    free(stack); 
                    free(postfix); 
                    return NULL; 
            }
            res->name = '?';
            if (!isalpha(matrix2->name))
                free(matrix2);
            if (!isalpha(matrix1->name)) 
                free(matrix1);
            stack[++top] = res;
            continue;
        }
    }
    matrix_sf *result = NULL;
    if (top == 0) {
        result = stack[top];
        result->name = name;
    }
    free(stack);
    free(postfix);
    return result;
}

matrix_sf *execute_script_sf(char *filename) {
    FILE *file = fopen(filename, "r");
    bst_sf *root = NULL;
    char *line = NULL;
    size_t cap = 0;
    ssize_t numberChs;
    matrix_sf *last = NULL;
    while ((numberChs = getline(&line, &cap, file)) != -1) {
        if (numberChs <= 0) 
            continue;
        while (numberChs > 0 && (line[numberChs-1] == '\n' || line[numberChs-1] == '\r'))
                line[--numberChs] = '\0'; 
        char *string = line;
        while (*string == ' ') 
            string++;
        if (!isupper((char)*string)) 
            continue; 
        char name = *string;
        char *equal = strchr(line, '=');
        if (!equal) 
            continue;
        char *rightSide = equal + 1;
        if (strchr(rightSide, '[')) {
            matrix_sf *matrix = create_matrix_sf(name, rightSide);
            if (matrix) {
                root = insert_bst_sf(matrix, root);
                last = matrix;
            }
        } else {
            matrix_sf *matrix = evaluate_expr_sf(name, rightSide, root);
            if (matrix) {
                root = insert_bst_sf(matrix, root);
                last = matrix;
            }
        }
    }
    free(line);
    fclose(file);
    (void)root;
    return last;
}

// This is a utility function used during testing. Feel free to adapt the code to implement some of
// the assignment. Feel equally free to ignore it.
matrix_sf *copy_matrix(unsigned int num_rows, unsigned int num_cols, int values[]) {
    matrix_sf *m = malloc(sizeof(matrix_sf)+num_rows*num_cols*sizeof(int));
    m->name = '?';
    m->num_rows = num_rows;
    m->num_cols = num_cols;
    memcpy(m->values, values, num_rows*num_cols*sizeof(int));
    return m;
}

// Don't touch this function. It's used by the testing framework.
// It's been left here in case it helps you debug and test your code.
void print_matrix_sf(matrix_sf *mat) {
    assert(mat != NULL);
    assert(mat->num_rows <= 1000);
    assert(mat->num_cols <= 1000);
    printf("%d %d ", mat->num_rows, mat->num_cols);
    for (unsigned int i = 0; i < mat->num_rows*mat->num_cols; i++) {
        printf("%d", mat->values[i]);
        if (i < mat->num_rows*mat->num_cols-1)
            printf(" ");
    }
    printf("\r\n");
}
