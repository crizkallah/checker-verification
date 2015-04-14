
/* Implementation types */

typedef unsigned Nat;
typedef Nat Vertex;
typedef Nat Edge_Id;
typedef int Parent_Edge;
typedef unsigned Num;

typedef struct Edge
{
    Vertex s;
    Vertex t;
} Edge;

typedef struct Graph
{
    Nat m;     // edges count
    Nat n;     // nodes count
    Edge* es;  // array of edges
    
} Graph;

int check_r(Graph* G, Vertex r, Parent_Edge* parent_edge, Num* num)
{
    return r < G->n && num[r] == 0 && parent_edge[r] < 0;
}

int check_parent_num(Graph* G, Vertex r, Parent_Edge* parent_edge, Num* num)
 {
    Edge_Id e;
    Vertex v;
    for (v = 0; v < G->n; v++)
     {
        e = (Edge_Id)parent_edge[v];
        if (v != r)
        {
          if (num[v] >= G->n) return 0;
          if (parent_edge[v] < 0) return 0;
          if (e >= G->m) return 0;
          if (G->es[e].t != v)  return 0;
          if (num[v] != num [G->es[e].s] + 1) return 0;
        }
    }
    return 1;
}

int check_connected(Graph* G, Vertex r, Parent_Edge* parent_edge, Num* num)
{
    int result = 
        check_r(G, r, parent_edge, num) &&
        check_parent_num(G, r, parent_edge, num);
    return result;
}

int main (int numc, char** argv)
{
return 0;
}
