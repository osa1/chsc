#include <igraph/igraph.h>

static igraph_bool_t find_callback(
        const igraph_vector_t *map12 /* large to small */,
        const igraph_vector_t *map21 /* small to large */,
        int (*callback)(double*))
{
    return (0 != callback(VECTOR(*map21)));
}

void find_graph_subisomorphisms(
        int smaller_nodes_count,
        int *smaller_colors,
        int smaller_edges_count,
        double *smaller_edges, // Who knows why they use double (igraph_real_t) for edge indexes...
        int larger_nodes_count,
        int *larger_colors,
        int larger_edges_count,
        double *larger_edges,

        /* Input array contains one element per node in smaller graph. Node
         * indexes are 1-based (so 0 can be used as a bad element in map12).
         * Return non-zero to continue search */
        int (*callback)(double *isomorphism))
{
    // Initialise "vectors" containing node edges
    igraph_vector_t larger_edges_vector, smaller_edges_vector;
    igraph_vector_view(&larger_edges_vector, larger_edges, larger_edges_count * 2);
    igraph_vector_view(&smaller_edges_vector, smaller_edges, smaller_edges_count * 2);

    // Initialise graphs themselves
    igraph_t larger_graph, smaller_graph;
    igraph_create(&larger_graph, &larger_edges_vector, larger_nodes_count, 1);
    igraph_create(&smaller_graph, &smaller_edges_vector, smaller_nodes_count, 1);

    // Initialise "vectors" containing node colors
    igraph_vector_int_t larger_colors_vector, smaller_colors_vector;
    igraph_vector_int_view(&larger_colors_vector, larger_colors, larger_nodes_count);
    igraph_vector_int_view(&smaller_colors_vector, smaller_colors, smaller_nodes_count);

    // Obtain the isomorphisms
    //igraph_get_subisomorphisms_vf2(&larger_graph, &smaller_graph, &larger_colors_vector, &smaller_colors_vector, NULL, NULL, &maps);
    igraph_subisomorphic_function_vf2(
            &larger_graph, &smaller_graph,
            &larger_colors_vector, &smaller_colors_vector,
            NULL, NULL,
            NULL, NULL,
            (igraph_isohandler_t*)find_callback,
            NULL, NULL,
            callback);

    // Destroy graphs (we don't need to destroy vectors since they are all views)
    igraph_destroy(&larger_graph);
    igraph_destroy(&smaller_graph);
}
