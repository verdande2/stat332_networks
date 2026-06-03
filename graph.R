# assumes node have an attribute: name
plottt <- function(g){
  set.seed(1)
  p <- ggraph::ggraph(g, layout = "fr") +
    geom_edge_fan(
      aes(
        color = V(g)$Carrier
      ),
      alpha = 0.8,
      strength = E(g)$weight
    ) +
    # geom_node_point(aes(size = coreness(g))) +
    geom_node_text(
      aes(
        label = name
      ),
      repel = TRUE,
      size = 3
    ) +

    # legends

    # guides
    # guides(
    # ) +

    labs(
      title = "Simple Plot"
    ) +
    theme_graph()
  p
}

print_igraph_attr <- function(graph) {
  print("--- Graph Attributes ------")
  print(graph_attr(graph))

  print("--- Vertex Attributes ------")
  print(vertex_attr(graph))

  print("--- Edge Attributes ------")
  print(edge_attr(graph))
}

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

#Note that we are specifying directed reachability for directed graphs
reachability_cohesion <- function(g, mode = c("undirected", "weak", "strong")) {
  mode <- match.arg(mode)
  n <- vcount(g)
  if (n <= 1) return(1)

  if (mode == "undirected") {
    g2 <- as_undirected(g, mode = "collapse",
                        edge.attr.comb = list(weight = "sum"))
    D <- distances(g2)
    reachable <- sum(D != Inf) - n      # exclude self-pairs
    total <- n * (n - 1)

  } else if (mode == "weak") {
    # treat as undirected for reachability
    comps <- components(g, mode = "weak")$membership
    comp_sizes <- table(comps)
    reachable <- sum(comp_sizes * (comp_sizes - 1))
    total <- n * (n - 1)

  } else if (mode == "strong") {
    D <- distances(g, mode = "out")
    reachable <- sum(D != Inf) - n
    total <- n * (n - 1)
  }

  cohesion <- reachable / total
  return(cohesion)
}

global_weighted_transitivity <- function(g, mode = c("undirected", "directed")) {
  mode <- match.arg(mode)

  if (mode == "undirected") {
    # This does nothing if the graph is already undirected but collapses a directed graph
    g2 <- as_undirected(g, mode = "collapse",
                        edge.attr.comb = list(weight = "sum"))
    local <- transitivity(g2, type = "weighted")
  } else {
    # Directed -> use directed weights but still based on Barrat formulation
    local <- transitivity(g, type = "weighted")
  }

  # Remove NA values (degree < 2)
  local <- local[!is.na(local)]

  # Average global weighted clustering
  mean(local)
}

print_big_fancy_summary_table <- function(graph) {
  big_fancy_igraph_table <- data.table(
    Label = c(
      "Connected?",
      "Simple?",
      "Loops?",
      "Multigraph?",
      "Weighted?",
      "Directed?",
      "Acyclic?",
      "Bipartite?",
      "Tree?",
      "Forest?",
      "Size:",
      "Components:",
      "Isolate Proportion:",
      "Density:",
      "Diameter:",
      "Average Path Length:"
    ),
    Value = c(
      is_connected(graph),
      is_simple(graph),
      any_loop(graph),
      any_multiple(graph),
      is_weighted(graph),
      is_directed(graph),
      is_acyclic(graph),
      is_bipartite(graph),
      is_tree(graph),
      is_forest(graph),
      gorder(graph),
      count_components(graph),
      sum(degree(graph) == 0) / gorder(graph),
      edge_density(simplify(graph)),
      diameter(graph),
      mean_distance(graph)
    )
  )
  big_fancy_igraph_table |>
    gt()
}

print_formatted_graph_summary_table <- function(g, title = "", subtitle = ""){
  graph_properties <- tribble(
    ~Property, ~Value,
    "Order", gorder(g),
    "Size", ecount(g), # size defined as # of edges in graph
    "Connnected", is_connected(g),
    "Directed", is_directed(g),
    "Acyclic", is_acyclic(g),
    "Weighted", is_weighted(g),
    "Simple", is_simple(g),
    "Has Loops", any_loop(g),
    "Is Multigraph", any_multiple(g),
    "Bipartite", is_bipartite(g),
    "Tree", is_tree(g),
    "Forest", is_forest(g)
  )

  graph_properties |>
    gt() |>
    tab_header(
      title = title,
      subtitle = subtitle
    ) |>
    # data_color(
    #   columns = everything(),   # columns to tint
    #   fn = function(cols) {
    #     category <- global_measures_table$Category
    #     category_colors[category]
    #   }
    # ) |> # TODO fix colors eventually
    fmt_number(columns = Value, rows = 1:2, decimals = 0, use_seps = TRUE) |> # special formatting for numeric values
    fmt_tf(columns = Value, rows = 3:length(Value), true_val = "✓", false_val = "✗", colors = c("#0072B2", "#E69F00")) |>  # special formating for the bools
    tab_options(table.font.size = 12)

}

# generic version of this function, without the third col of expected values
# editor's note: splitting table into two subtables, first for T/F values and the second for the component counts
print_metadata_summary_TF_table <- function(graph) {
  tbl_TF <- data.table(
    Label = c(
      "Directed?",
      "Weighted?",
      "Not Simple?",
      "Has Multiple Edges?",
      "Weakly Connected?",
      "Strongly Connected?"
    ),
    Value = c(
      igraph::is_directed(g),
      igraph::is_weighted(g),
      !igraph::is_simple(g),
      length(E(g)) > 1,
      is_connected(g, mode = "weak"), # mode = weak is the default
      is_connected(g, mode = "strong")
    )
  )
  colnames(tbl_TF) <- c("Label", "Value")
  tbl_TF |>
    gt() |>
    fmt_tf(columns = where(~ is.numeric(.x)), tf_style = "true-false")
}

print_metadata_summary_components_table <- function(g) {
  tbl_components <- data.table(
    Label = c(
      "# of Strongly-connected components:",
      "# of Weakly-connected components:"
    ),
    Value = c(
      components(g, mode = "strong")$no,
      components(g, mode = "weak")$no # mode = weak is the default
    )
  )
  colnames(tbl_components) <- c("Label", "Value")
  tbl_components |>
    gt() |>
    fmt_number(columns = where(~ is.numeric(.x)), decimals = 0, use_seps = TRUE)
}

show_k_core_plots <- function(g){
  k_core_g <- coreness(g, mode = "all")

  V(g)$core <- k_core_g # storing the already calculated k-core in the vertices' core attr

  set.seed(1) # static seed for repeatability FOR NOW
  L <- layout_with_fr(g) # Fruchterman-Reingold layout

  ks <- sort(unique(V(g)$core)) # sorted vector of distinct k-core values
  ks <- ks[ks > 0]  # drop 0-core isolates

  # okay, breaking this down, looks like we are mapping over our distinct k-core values (in order, per sort call above), expecting a list return type and performing an anonymous function that is long enough to where it probably should be a _named_ function. Let's poke at it and comment on what it's doing...
  plots <- lapply(ks, function(k){
    keep <- V(g)$core >= k # for any k passed in, keep holds the bool vector of vertex indices with >=k core
    sg <- induced_subgraph(g, vids = V(g)[keep]) # making a new subgraph consisting of just the vertices that have >= current k-core (and any connecting edges between them)

    # subset the full-graph layout to this subgraph's vertices (keeps positions stable)
    idx <- as.integer(V(g)[keep])        # vertex ids in original graph
    Lk  <- L[idx, , drop = FALSE] # subsetting the fr layout with the "keep" vertex ids/indices, the entire "row", and passing drop=FALSE ensures we get a df back out

    # passing along our subgraph to ggraph, manual layout with our Lk values from above loc
    ggraph(sg, layout = "manual", x = Lk[,1], y = Lk[,2]) +

      # now, adding relatively transparent mid gray edges connecting the vertices
      geom_edge_link(alpha = 0.25, colour = "grey60") +

      # adding the vertices, colored based on their k-core value, static size of 2.5
      geom_node_point(aes(color = core), size = 2.5) +

      # adding text labels, pulled from name attr, static size of 3, with a vertical adjustment
      geom_node_text(aes(label = label),
                     size = 3,
                     vjust = 1.5) +

      # setting the color scale, option D is viridis (the green/blue gradient one), excellent choice, the end param sets the end of the color hue range from [0,1] to [0, 0.95]
      # calling scale_color_viridis_c(), noting the _c ending, confused me for a while now, and it just dawned on me after reading the ggplot2 docs that that _c doesn't mean color option c, it stands for continuous, as opposed to d for discrete, or apparently b for binned color maps... Today I learned a thing...
      scale_color_viridis_c(option = "C", end = 0.95) +

      # add a plot title, indicating the current k value, as well as the number of vertices and edges in the subgraph
      ggtitle(paste0(k, "-core (core ≥ ", k, "), n=", vcount(sg), ", m=", ecount(sg))) +

      # blank theme with just default font size set
      theme_void(base_size = 11) +

      # nullify the legend, and set the plot title to be smaller font face and bolded
      theme(legend.position = "none",
            plot.title = element_text(size = 10, face = "bold"))

    # no explicit return, so that ggraph is the return obj
  })

  # this will distribute the plots among a 2-col grid layout, for as many plots exist in ... well, plots. I'm relating this to patchwork or kinda like faceting behavior... edit 27 minutes later, when I notice what package wrap_plots is from, and didn't notice when copying its library call to top of file.... Argh!
  wrap_plots(plots, ncol = 2)
}

show_k_core_shell_plots <- function(g){
  # alright, looks like we're applying a similar function as above over our kept k-cores, ks, expecting a list back and assigning to shell_plots
  k_core_g <- coreness(g, mode = "all")

  V(g)$core <- k_core_g # storing the already calculated k-core in the vertices' core attr

  set.seed(1) # static seed for repeatability FOR NOW
  L <- layout_with_fr(g) # Fruchterman-Reingold layout

  ks <- sort(unique(V(g)$core)) # sorted vector of distinct k-core values

  shell_plots <- lapply(ks, function(k){
    # identical as above, calculating k-cores and making a subgraph of them and their edges
    keep <- V(g)$core == k
    sg <- induced_subgraph(g, vids = V(g)[keep])

    # again, getting the indices and doing some magic before indexing the layout and storing the coords
    idx <- as.integer(V(g)[keep])
    Lk  <- L[idx, , drop = FALSE]

    ggraph(sg, layout = "manual", x = Lk[,1], y = Lk[,2]) + # same manual layout

      # this line differs. static vertex size and color... Hmmmm...
      geom_node_point(size = 2.5, color = "#2C7FB8") +

      # identical
      geom_node_text(aes(label = name),
                     size = 3,
                     vjust = 1.5) +

      # the key difference is a missing call to any ggraph function that adds edges/links, so only the vertices will display.

      # title the plot with the k-shell value, k-core value, and the vertex count
      ggtitle(paste0(k, "-shell (core == ", k, "), n=", vcount(sg))) +

      # blank theme with base font size 11
      theme_void(base_size = 11)
  })

  # wraps the plots, however many there may be, in a 2-col grid style layout
  wrap_plots(shell_plots, ncol = 2)
}

# TODO line by line debug this
conductance_of_set <- function(g, S, weights = E(g)$weight) {
  # if weights=null is passed, start weights at vector of 1s
  if (is.null(weights)) weights <- rep(1, ecount(g))

  S <- as.integer(S) # integerize the set
  S_flag <- rep(FALSE, vcount(g)) # set flags to false for all vertices
  S_flag[S] <- TRUE

  ep <- ends(g, E(g), names = FALSE)
  crossing <- xor(S_flag[ep[, 1]], S_flag[ep[, 2]])
  cut_w <- sum(weights[crossing], na.rm = TRUE)

  # weighted degrees
  if (!is.null(E(g)$weight)) {
    deg_w <- strength(g, vids = V(g), mode = "all", weights = E(g)$weight)
  } else {
    deg_w <- degree(g)
  }

  vol_S  <- sum(deg_w[S])
  vol_cS <- sum(deg_w[!S_flag])

  denom <- min(vol_S, vol_cS)
  if (denom == 0) return(0)
  cut_w / denom
}

find_fiedlers_number <- function(g){
  Laplacian <- laplacian_matrix(g, weights = E(g)$weight, normalization = "symmetric")
  eigenvalues <- eigen(Laplacian, symmetric = TRUE, only.values = TRUE)$values
  lambda_2 <- eigenvalues[length(eigenvalues) - 1]
  lambda_2
}

# TODO line by line this function and comment it all out
fiedler_sweep_cut <- function(g) {

  # Make sure it's undirected and weighted sensibly
  if (is_directed(g)) {
    g <- as_undirected(g, mode = "collapse", edge.attr.comb = list(weight = "sum"))
  }

  # Compute symmetric normalized Laplacian
  L <- laplacian_matrix(g, weights = E(g)$weight, normalization = "symmetric")

  # Eigen-decomposition: eigenvalues in *descending order*
  ev <- eigen(L, symmetric = TRUE)

  # Fiedler vector = eigenvector for second-smallest eigenvalue
  fiedler_vec <- ev$vectors[, ncol(ev$vectors) - 1]

  # Sweep: sort vertices by Fiedler values
  ord <- order(fiedler_vec)

  best_phi <- Inf
  best_S <- NULL

  # seek out lowest conductance of set S on g
  for (t in 1:(length(ord) - 1)) {
    S <- ord[1:t]
    phi_S <- conductance_of_set(g, S)
    if (phi_S < best_phi) {
      best_phi <- phi_S
      best_S <- S
    }
  }

  list(
    phi = best_phi,
    S = best_S,
    fiedler_vector = fiedler_vec
  )
}

# TODO line by line this func
page_rank_sweep_cut <- function(g, alpha = 0.15) {

  if (is.directed(g)) {
    g <- as.undirected(g, mode = "collapse", edge.attr.comb = list(weight = "sum"))
  }

  # Weighted PageRank
  pr <- page_rank(g, algo = "prpack", damping = 1 - alpha,
                  weights = E(g)$weight)$vector

  # Normalize by weighted degree (this matters!)
  deg <- strength(g, vids = V(g), mode = "all", weights = E(g)$weight)
  score <- pr / deg

  ord <- order(score, decreasing = TRUE)  # highest score first

  best_phi <- Inf
  best_S <- NULL

  for (t in 1:(length(ord) - 1)) {
    S <- ord[1:t]
    phi <- conductance_of_set(g, S)
    if (phi < best_phi) {
      best_phi <- phi
      best_S <- S
    }
  }

  list(
    phi = best_phi,
    vertex_ids = best_S,
    vertex_names = V(g)$name[best_S],
    page_rank = pr,
    score = score
  )
}

# TODO line by line and comment
centr_clo_weighted <- function(g) {
  # convert tie strength → distance
  d <- 1 / E(g)$weight

  # weighted closeness
  C <- closeness(g, weights = d)

  # remove Inf or NA (isolates)
  C <- C[is.finite(C)]

  C_max <- max(C)
  num <- sum(C_max - C)
  #Set a theoretical maximum based on the total distance represented in the network
  denom <- (length(C) - 1) * C_max

  if (denom == 0) return(0)
  num / denom
}

# TODO line by line
centr_betw_weighted <- function(g) {
  # Convert strength → distance
  d <- 1 / E(g)$weight # reciprocalize!

  # weighted betweenness
  b <- betweenness(g, directed = FALSE, weights = d)

  b_max <- max(b)
  num <- sum(b_max - b)
  denom <- (length(b) - 1) * b_max

  if (denom == 0) return(0)
  num / denom
}

# TODO line by line comment
centr_eigen_weighted <- function(g) {
  # weighted EC scores
  ec <- eigen_centrality(g, weights = E(g)$weight)$vector

  # remove missing values (rare but can occur)
  ec <- ec[is.finite(ec)]

  ec_max <- max(ec)

  # Freeman numerator
  num <- sum(ec_max - ec)

  # theoretical maximum for normalized star
  # (one node gets ec_max, all others get 0)
  denom <- (length(ec) - 1) * ec_max

  if (denom == 0) return(0)

  num / denom
}

plot_dist <- function(x,
                      title = NULL,
                      xlab = NULL,
                      fill_color = "#4C72B0",
                      density_color = "#DD8452",
                      bins = 30) {

  x <- x[is.finite(x)]
  df <- data.frame(value = x)

  p_hist <- ggplot(df, aes(x = value)) +
    geom_histogram(
      aes(y = after_stat(density)),
      bins = bins,
      fill = fill_color,
      color = "white",
      alpha = 0.85
    ) +
    geom_density(
      color = density_color,
      linewidth = 1.1,
      adjust = 1.1
    ) +
    labs(
      title = title,
      x = xlab,
      y = "Density"
    ) +
    theme_minimal(base_size = 13) +
    theme(
      plot.title = element_text(face = "bold"),
      panel.grid.minor = element_blank()
    )

  p_box <- ggplot(df, aes(x = value, y = "")) +
    geom_boxplot(
      fill = fill_color,
      alpha = 0.55,
      outlier.color = density_color,
      outlier.size = 2
    ) +
    theme_minimal(base_size = 13) +
    theme(
      axis.title.y = element_blank(),
      axis.text.y  = element_blank(),
      axis.ticks.y = element_blank(),
      panel.grid   = element_blank()
    ) +
    labs(x = xlab)

  gridExtra::grid.arrange(p_hist, p_box, heights = c(3, 1))
}
