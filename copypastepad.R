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



nne_in <- sapply(E(g), function(e) {
  v <- ends(g, e)
  (deg_in[v[1]] - 1) + (deg_in[v[2]] - 1)
})

nne_out <- sapply(E(g), function(e) {
  v <- ends(g, e)
  (deg_out[v[1]] - 1) + (deg_out[v[2]] - 1)
})


# Local Clustering Coefficient
cc_local <- transitivity(as.undirected(g, mode = "collapse"),
                         type = "local", isolates = "zero")


le_in <- local_efficiency(g, directed = TRUE, mode = "in")
le_out <- local_efficiency(g, directed = TRUE, mode = "out")



