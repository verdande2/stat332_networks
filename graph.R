strong_articulation_points <- function(g) {
  base <- components(g, mode = "strong")$no  # This is the number of nodes in the strongly connected component.
  vids <- V(g)  # the vertex ideas from the graph g
  out <- vids[sapply(vids, function(v) {
    components(delete_vertices(g, v), mode = "strong")$no > base
  })] # this one line has so much going on, but I see what it's doing... succinct.
  out # Return the ones that increase the number of components of the original graph
}


strong_bridges <- function(g) {
  base <- components(g, mode = "strong")$no
  eids <- E(g)  #Get the edge ids of g
  keep <- sapply(eids, function(e) {
    components(delete_edges(g, e), mode = "strong")$no > base # Figure out which edges fracture the graph when removed.
  })
  eids[keep]
}



nne_edge_centrality <- function(g, deg_tot) {
  sapply(E(g), function(e) {
    v <- ends(g, e)
    (deg_tot[v[1]] - 1) + (deg_tot[v[2]] - 1)
  })
}
nne_in <- sapply(E(g), function(e) {
  v <- ends(g, e)
  (deg_in[v[1]] - 1) + (deg_in[v[2]] - 1)
})
nne_out <- sapply(E(g), function(e) {
  v <- ends(g, e)
  (deg_out[v[1]] - 1) + (deg_out[v[2]] - 1)
})


deg_in  <- degree(g, mode = "in")
deg_out <- degree(g, mode = "out")


deg_in_cent <- degree(g, v = V(g), mode = "in", loops = TRUE, normalized = TRUE)
deg_out_cent <- degree(g, v = V(g), mode = "out", loops = TRUE, normalized = TRUE)


in_core <- coreness(g, mode = "in")
out_core <- coreness(g, mode = "out")


btw_cent <- betweenness(g, directed = TRUE, normalized = TRUE)

clo_in  <- closeness(g, mode = "in",  normalized = TRUE)
clo_out  <- closeness(g, mode = "out",  normalized = TRUE)

# Eigen not for directed graphs

pr <- page_rank(g, directed = TRUE)$vector

# Bonacich Centrality
bon <- power_centrality(g, exponent = 0.1, rescale = TRUE)



ebtw <- edge_betweenness(g, directed = TRUE)



nne <- nne_edge_centrality(g, deg_in + deg_out)


# Local Clustering Coefficient
cc_local <- transitivity(as.undirected(g, mode = "collapse"),
                         type = "local", isolates = "zero")


le_in <- local_efficiency(g, directed = TRUE, mode = "in")
le_out <- local_efficiency(g, directed = TRUE, mode = "out")



