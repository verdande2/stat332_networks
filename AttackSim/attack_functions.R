# Network Attack Functions for both Removal and Infection
#  Works with both targeted and random attacks
## TODO:  Implement Edge level attacks
## TODO:  Implement other forms of attacks such as rate limiting, overloading, etc...
## TODO:  Implement rewiring attacks


# I don't remember why I defined this.  :)  
`%||%` <- function(a, b) if (!is.null(a)) a else b

# Making sure that the vertex id's are unique and not reindexed.
ensure_vertex_uid <- function(g) {
  if (is.null(igraph::vertex_attr(g, "uid"))) {
    igraph::V(g)$uid <- seq_len(igraph::vcount(g))
  }
  g
}

vertex_key <- function(g, vids) {
  nm <- igraph::vertex_attr(g, "name")
  if (!is.null(nm)) return(as.character(nm[vids]))
  
  uid <- igraph::vertex_attr(g, "uid")
  if (!is.null(uid)) return(as.character(uid[vids]))
  
  as.character(vids)
}


# Metrics validation helper ----
  # checks to make sure the user defined metrics are in the correct format
validate_metrics <- function(metrics, n) {
  stopifnot(is.list(metrics),
            all(c("node","meso","graph") %in% names(metrics)),
            is.list(metrics$node),
            is.list(metrics$meso),
            is.list(metrics$graph))
  
  # node metrics must be numeric length n
  for (k in names(metrics$node)) {
    v <- metrics$node[[k]]
    if (!is.numeric(v) || length(v) != n) {
      stop(sprintf("metrics$node$%s must be numeric length %d", k, n))
    }
  }
  # meso metrics can be scalar or length n
  for (k in names(metrics$meso)) {
    v <- metrics$meso[[k]]
    if (!is.numeric(v) || !(length(v) == 1 || length(v) == n)) {
      stop(sprintf("metrics$meso$%s must be numeric length 1 or %d", k, n))
    }
  }
  # graph metrics must be scalar
  for (k in names(metrics$graph)) {
    v <- metrics$graph[[k]]
    if (!is.numeric(v) || length(v) != 1) {
      stop(sprintf("metrics$graph$%s must be numeric scalar", k))
    }
  }
  TRUE
}

## retrieval for metrics ----
get_metric_vector <- function(metrics, level, metric) {
  #again, missnamed micro as node bcause I'm an idiot and forgot about edges
  if (!level %in% c("node","meso","graph")) stop("level must be node|meso|graph") 
  if (is.null(metrics[[level]][[metric]])) {
    stop(sprintf("Metric %s not found in metrics$%s", metric, level))
  }
  metrics[[level]][[metric]]
}


# Validation for stage definition ----
## checks to make sure the suer defined stage is proper according to these rules.
validate_stage <- function(stage) {
  stopifnot(is.list(stage), !is.null(stage$id), !is.null(stage$mode))
  stopifnot(stage$mode %in% c("removal","infection","infection_removal"))
  
  # selection spec (may be unused for pure spread rounds, but present for removal targeting)
  if (!is.null(stage$selection)) {
    sel <- stage$selection
    stopifnot(sel$rule %in% c("n","pct","threshold"))
    stopifnot(sel$level %in% c("node","meso"))
    stopifnot(!is.null(sel$metric))
    if (sel$rule == "threshold") stopifnot(!is.null(sel$tau))
    if (sel$rule == "n") stopifnot(!is.null(sel$n))
    if (sel$rule == "pct") stopifnot(!is.null(sel$pct))
  }
  
  # loop spec
  stopifnot(!is.null(stage$loop), stage$loop$type %in% c("rounds","until"))
  if (stage$loop$type == "rounds") stopifnot(!is.null(stage$loop$max_rounds))
  if (stage$loop$type == "until")  stopifnot(is.function(stage$loop$until_fun))
  
  # infection requirements
  if (stage$mode %in% c("infection","infection_removal")) {
    stopifnot(!is.null(stage$infection),
              !is.null(stage$infection$update),
              !is.null(stage$infection$update$type),
              !is.null(stage$infection$update$params))
  }
  
  if (stage$mode == "infection_removal") {
    stopifnot(!is.null(stage$removal_prob), !is.null(stage$removal_prob$p_remove))
  }
  
  TRUE
}

## call for the validation function for all stages.----
validate_stages <- function(stages) {
  stopifnot(is.list(stages), length(stages) >= 1)
  for (s in stages) validate_stage(s)
  TRUE
}


# Initialization for state and trajectory ----
init_state <- function(g0) {
  n0 <- igraph::vcount(g0)
  list(
    t_global = 0L,
    stage_index = 0L,
    t_stage = 0L,
    n0 = n0
  )
}

init_trajectory <- function(g0, stages, seed, version) {
  list(
    meta = list(
      seed = seed,
      version = version,
      stages = stages,
      start_time = Sys.time(),
      graph_info = list(
        directed = igraph::is_directed(g0),
        weighted = !is.null(igraph::edge_attr(g0, "weight")),
        n0 = igraph::vcount(g0),
        m0 = igraph::ecount(g0)
      )
    ),
    rounds = list(),
    graphs = list(g0)  # store initial graph snapshot
  )
}


eligible_vertices <- function(g, stage) {
  elig <- stage$eligibility %||% list(set="all", fun=NULL)
  
  if (!is.null(elig$fun) && is.function(elig$fun)) {
    keep <- elig$fun(g)
    return(which(keep))
  }
  
  if ((elig$set %||% "all") == "non_infected") {
    inf <- igraph::vertex_attr(g, "infected")
    if (is.null(inf)) inf <- rep(FALSE, igraph::vcount(g))
    return(which(!inf))
  }
  
  seq_len(igraph::vcount(g))
}

# Eligibility and selection for Attack ----
select_vertices <- function(g, metrics_pre, stage) {
  sel <- stage$selection %||% NULL
  E <- eligible_vertices(g, stage)
  
  if (is.null(sel)) {
    # If no selection is defined, return empty selection (spread-only mode)
    return(list(eligible_ids=E, selected_ids=integer(0), selected_values=numeric(0)))
  }
  
  scores <- get_metric_vector(metrics_pre, sel$level, sel$metric)
  scores_E <- scores[E]
  
  if ((sel$type %||% "targeted") == "random") {
    # random selection ignores scores
    if (sel$rule == "n") {
      k <- min(sel$n, length(E))
      S <- if (k > 0) sample(E, k) else integer(0)
    } else if (sel$rule == "pct") {
      k <- min(max(1, floor(sel$pct * length(E))), length(E))
      S <- if (k > 0) sample(E, k) else integer(0)
    } else {
      stop("Random + threshold is undefined (threshold needs scores).")
    }
    return(list(eligible_ids=E, selected_ids=S, selected_values=scores[S]))
  }
  
  # targeted selection (dynamic: metrics_pre recomputed each round)
  if (sel$rule == "threshold") {
    S <- E[which(scores_E >= sel$tau)]  # remove ALL above tau
  } else if (sel$rule == "n") {
    ord <- order(scores_E, decreasing=TRUE, na.last=NA)
    k <- min(sel$n, length(ord))
    S <- if (k > 0) E[ord[seq_len(k)]] else integer(0)
  } else if (sel$rule == "pct") {
    ord <- order(scores_E, decreasing=TRUE, na.last=NA)
    k <- min(max(1, floor(sel$pct * length(E))), length(ord))
    S <- if (k > 0) E[ord[seq_len(k)]] else integer(0)
  } else stop("Unknown selection rule")
  
  list(eligible_ids=E, selected_ids=S, selected_values=scores[S])
}

edge_trans_prob <- function(p0, w, rule = c("contacts","linear","power","logistic"),
                            scale = 1, exponent = 1, k = 1) {
  rule <- match.arg(rule)
  w <- as.numeric(w)
  w[!is.finite(w)] <- 1
  w <- pmax(w, 0)
  
  if (rule == "contacts") {
    # weight = number of contacts (or exposure intensity after scaling)
    # p = 1 - (1 - p0)^(w*scale)
    ws <- w * scale
    return(1 - (1 - p0)^(ws))
  }
  if (rule == "linear") {
    # p = min(1, p0 * (w*scale))
    return(pmin(1, p0 * (w * scale)))
  }
  if (rule == "power") {
    # p = min(1, p0 * (w*scale)^exponent)
    return(pmin(1, p0 * (w * scale)^exponent))
  }
  # logistic
  # p = 1/(1 + exp(-k*(w*scale))) * p0_max; here we cap at 1 by default
  ws <- w * scale
  return(pmin(1, p0 * (1 / (1 + exp(-k * (ws - 1))))))
}


# Mechanisms for Infection ----
ensure_infection_attrs <- function(g) {
  if (is.null(igraph::vertex_attr(g, "infected"))) igraph::V(g)$infected <- FALSE
  if (is.null(igraph::vertex_attr(g, "infected_age"))) igraph::V(g)$infected_age <- 0L
  g
}

infection_update <- function(g, stage) {
  g <- ensure_infection_attrs(g)
  type <- stage$infection$update$type
  p <- stage$infection$update$params
  
  n <- igraph::vcount(g)
  infected <- igraph::V(g)$infected
  newly <- rep(FALSE, n)
  
  # ---- Common params for weighted/directed transmission
  # base probability per "unit contact"
  p_trans <- p$p_transmit %||% NULL
  
  # direction mode for neighbor traversal
  # - undirected graphs: "all" is fine
  # - directed graphs: "out" means infected -> susceptible along outgoing edges
  dir_mode <- p$direction_mode %||% "all"
  
  # weights
  weight_attr <- p$weight_attr %||% "weight"   # igraph convention [5](https://r.igraph.org/reference/is_weighted.html)[6](https://www.rdocumentation.org/packages/igraph/versions/1.3.5/topics/is_weighted)
  weight_rule <- p$weight_rule %||% "contacts" # "contacts" is a good default if weight=contact count
  weight_scale <- p$weight_scale %||% 1
  weight_exp <- p$weight_exponent %||% 1
  weight_k <- p$weight_k %||% 1
  
  # Fetch weights if present; default to 1
  w_all <- igraph::edge_attr(g, weight_attr)
  has_w <- !is.null(w_all)
  
  # Helper to get edge weights for pairs (u -> v) efficiently
  get_w_uv <- function(u, vs) {
    if (!has_w) return(rep(1, length(vs)))
    # get.edge.ids expects a two-column matrix of vertex ids (from,to)
    eids <- igraph::get.edge.ids(g, vp = cbind(rep(u, length(vs)), vs), directed = TRUE, error = FALSE)
    # get.edge.ids returns 0 when edge not found
    w <- rep(1, length(vs))
    ok <- eids > 0
    if (any(ok)) w[ok] <- w_all[eids[ok]]
    w
  }
  
  if (type == "SI") {
    p_trans <- p_trans %||% stop("SI requires params$p_transmit")
    
    inf_ids <- which(infected)
    if (length(inf_ids) > 0) {
      # accumulate per-susceptible complement probability: q[v] = prod(1 - p_edge)
      q <- rep(1, n)
      
      for (u in inf_ids) {
        nbr_ids <- as.integer(igraph::neighbors(g, u, mode = dir_mode))
        if (length(nbr_ids) == 0) next
        sus <- nbr_ids[!infected[nbr_ids]]
        if (length(sus) == 0) next
        
        w_uv <- get_w_uv(u, sus)
        p_uv <- edge_trans_prob(p0 = p_trans, w = w_uv,
                                rule = weight_rule, scale = weight_scale,
                                exponent = weight_exp, k = weight_k)
        q[sus] <- q[sus] * (1 - p_uv)
      }
      
      p_sus <- 1 - q
      # only susceptibles can be newly infected
      sus_ids <- which(!infected)
      newly[sus_ids] <- runif(length(sus_ids)) < p_sus[sus_ids]
      infected <- infected | newly
    }
    
  } else if (type == "SIS") {
    p_trans <- p_trans %||% stop("SIS requires params$p_transmit")
    p_rec  <- p$p_recover %||% stop("SIS requires params$p_recover")
    
    # recovery
    inf_ids <- which(infected)
    if (length(inf_ids) > 0) infected[inf_ids] <- !(runif(length(inf_ids)) < p_rec)
    
    # spread from remaining infected
    inf_ids <- which(infected)
    if (length(inf_ids) > 0) {
      q <- rep(1, n)
      
      for (u in inf_ids) {
        nbr_ids <- as.integer(igraph::neighbors(g, u, mode = dir_mode))
        if (length(nbr_ids) == 0) next
        sus <- nbr_ids[!infected[nbr_ids]]
        if (length(sus) == 0) next
        
        w_uv <- get_w_uv(u, sus)
        p_uv <- edge_trans_prob(p0 = p_trans, w = w_uv,
                                rule = weight_rule, scale = weight_scale,
                                exponent = weight_exp, k = weight_k)
        q[sus] <- q[sus] * (1 - p_uv)
      }
      
      p_sus <- 1 - q
      sus_ids <- which(!infected)
      newly[sus_ids] <- runif(length(sus_ids)) < p_sus[sus_ids]
      infected <- infected | newly
    }
    
  } else if (type == "threshold") {
    # keep your existing threshold code
    thr <- p$frac_threshold %||% stop("threshold requires params$frac_threshold")
    for (v in which(!infected)) {
      nbr_ids <- as.integer(igraph::neighbors(g, v, mode="all"))
      if (length(nbr_ids) == 0) next
      frac_inf <- sum(infected[nbr_ids]) / length(nbr_ids)
      if (frac_inf >= thr) newly[v] <- TRUE
    }
    infected <- infected | newly
    
  } else if (type == "independent_failure") {
    p_fail <- p$p_fail %||% stop("independent_failure requires params$p_fail")
    newly[!infected] <- runif(sum(!infected)) < p_fail
    infected <- infected | newly
    
  } else {
    stop(sprintf("Unknown infection update type: %s", type))
  }
  
  # Update attrs: newly infected get age=1; existing infected age increments
  igraph::V(g)$infected <- infected
  
  age <- igraph::V(g)$infected_age
  age[infected] <- age[infected] + 1L
  age[newly] <- 1L
  age[!infected] <- 0L
  igraph::V(g)$infected_age <- age
  
  list(g=g, newly_ids=which(newly), infected_total=sum(infected))
}

# Infection seeding ----
infection_seed <- function(g, state, stage, metrics_pre) {
  g <- ensure_infection_attrs(g)
  
  seed <- stage$infection$seed %||% NULL
  if (is.null(seed)) return(list(g=g, seeded_ids=integer(0)))
  
  n <- igraph::vcount(g)
  if (n == 0) return(list(g=g, seeded_ids=integer(0)))
  
  # Optional: allow users to constrain seeding to eligible set (does not require it)
  # If stage$eligibility exists, we interpret it the same way as selection eligibility
  E <- tryCatch(eligible_vertices(g, stage), error=function(e) seq_len(n))
  if (length(E) == 0) return(list(g=g, seeded_ids=integer(0)))
  
  S <- integer(0)
  
  if (seed$method == "pct_random") {
    # seed$value is a fraction of total nodes (or eligible nodes, if eligibility provided)
    frac <- seed$value %||% stop("pct_random requires seed$value (fraction)")
    if (!is.numeric(frac) || length(frac) != 1) stop("pct_random seed$value must be numeric scalar")
    
    k <- max(1L, floor(frac * length(E)))
    k <- min(k, length(E))
    S <- if (k > 0) sample(E, k) else integer(0)
    
  } else if (seed$method == "metric_targeted") {
    # Choose metric/level defaults similarly to your original logic
    lvl <- seed$level %||% (stage$selection$level %||% "node")
    met <- seed$metric %||% (stage$selection$metric %||% stop("Need metric for metric_targeted seeding"))
    
    scores <- get_metric_vector(metrics_pre, lvl, met)
    
    # ---- Critical guardrail: must be length-n numeric vector for ranking vertices
    if (!is.numeric(scores)) stop("metric_targeted requires numeric metric vector")
    if (length(scores) != n) {
      stop(sprintf(
        "metric_targeted seeding requires a length-n metric vector (n=%d). Got length %d for metrics$%s$%s",
        n, length(scores), lvl, met
      ))
    }
    
    # Rank only eligible vertices; drop NAs
    scores_E <- scores[E]
    ordE <- order(scores_E, decreasing=TRUE, na.last=NA)
    if (length(ordE) == 0) return(list(g=g, seeded_ids=integer(0)))
    
    batch_type <- seed$batch_type %||% "pct"
    val <- seed$value %||% stop("metric_targeted requires seed$value")
    
    if (batch_type == "pct") {
      if (!is.numeric(val) || length(val) != 1) stop("metric_targeted pct seed$value must be numeric scalar")
      k <- max(1L, floor(val * length(E)))
    } else {
      # treat as "n"
      if (!is.numeric(val) || length(val) != 1) stop("metric_targeted n seed$value must be numeric scalar")
      k <- as.integer(val)
      if (is.na(k) || k < 1L) k <- 1L
    }
    
    k <- min(k, length(ordE))
    S <- if (k > 0) E[ordE[seq_len(k)]] else integer(0)
    
  } else {
    stop("Unknown seed$method")
  }
  
  # Apply seeding
  S <- as.integer(S)
  if (length(S) == 0) return(list(g=g, seeded_ids=integer(0)))
  
  igraph::V(g)$infected[S] <- TRUE
  igraph::V(g)$infected_age[S] <- 1L
  
  list(g=g, seeded_ids=S)
}

edge_trans_prob <- function(p0, w, rule = c("contacts","linear","power","logistic"),
                            scale = 1, exponent = 1, k = 1) {
  rule <- match.arg(rule)
  w <- as.numeric(w)
  w[!is.finite(w)] <- 1
  w <- pmax(w, 0)
  
  if (rule == "contacts") {
    # weight = number of contacts (or exposure intensity after scaling)
    # p = 1 - (1 - p0)^(w*scale)
    ws <- w * scale
    return(1 - (1 - p0)^(ws))
  }
  if (rule == "linear") {
    # p = min(1, p0 * (w*scale))
    return(pmin(1, p0 * (w * scale)))
  }
  if (rule == "power") {
    # p = min(1, p0 * (w*scale)^exponent)
    return(pmin(1, p0 * (w * scale)^exponent))
  }
  # logistic
  # p = 1/(1 + exp(-k*(w*scale))) * p0_max; here we cap at 1 by default
  ws <- w * scale
  return(pmin(1, p0 * (1 / (1 + exp(-k * (ws - 1))))))
}

# Removal Applied ----
apply_removal <- function(g, selection) {
  removed_vids <- selection$selected_ids
  if (length(removed_vids) == 0) return(list(g=g, removed_vids=integer(0)))
  g2 <- igraph::delete_vertices(g, removed_vids)
  list(g=g2, removed_vids=removed_vids)
}

apply_infection <- function(g, stage) {
  upd <- infection_update(g, stage)
  list(g=upd$g, newly_ids=upd$newly_ids, infected_total=upd$infected_total)
}

apply_infection_removal <- function(g, stage) {
  upd <- infection_update(g, stage)
  g2 <- upd$g
  
  p_remove <- stage$removal_prob$p_remove
  min_age  <- stage$removal_prob$min_age %||% 0L
  
  infected <- igraph::V(g2)$infected
  age <- igraph::V(g2)$infected_age
  candidates <- which(infected & age >= min_age)
  
  to_remove <- candidates[runif(length(candidates)) < p_remove]
  if (length(to_remove) > 0) {
    g2 <- igraph::delete_vertices(g2, to_remove)
  }
  
  list(g=g2,
       newly_ids=upd$newly_ids,
       infected_total=upd$infected_total,
       removed_vids=to_remove)
}

# logging for pre and post metrics ----
make_round_record <- function(t_global, stage_index, stage_id, t_stage,
                              g_pre, g_post,
                              metrics_pre, metrics_post,
                              selection, effect) {
  list(
    t_global = t_global,
    stage = list(index=stage_index, id=stage_id, t_stage=t_stage),
    graph = list(n_pre=igraph::vcount(g_pre), m_pre=igraph::ecount(g_pre),
                 n_post=igraph::vcount(g_post), m_post=igraph::ecount(g_post)),
    metrics = list(pre=metrics_pre, post=metrics_post),
    selection = selection,
    effect = effect
  )
}


# Driver Function ----
attack_graph <- function(g0, stages, scoring_fun,
                         seed = NULL, version = "v1_vertices",
                         store_graphs = TRUE) {
  
  if (!is.null(seed)) set.seed(seed)
  validate_stages(stages)
  
  state <- init_state(g0)
  traj  <- init_trajectory(g0, stages, seed, version)
  
  g <- g0
  
  for (si in seq_along(stages)) {
    stage <- stages[[si]]
    state$stage_index <- si
    state$t_stage <- 0L
    
    # Stage start: compute metrics_pre for seeding if needed
    metrics0 <- scoring_fun(g, state)
    validate_metrics(metrics0, igraph::vcount(g))
    
    # Optional seeding for infection stages
    seeded_ids <- integer(0)
    if (stage$mode %in% c("infection","infection_removal")) {
      g_seed_pre <- g  # <-- capture pre-seed snapshot for correct logging
      
      seed_res <- infection_seed(g, state, stage, metrics0)
      g <- seed_res$g
      seeded_ids <- seed_res$seeded_ids
      
      # After seeding, record seed event as "round 0" of this stage (optional)
      if (length(seeded_ids) > 0) {
        metrics_pre  <- metrics0
        metrics_post <- scoring_fun(g, state)
        validate_metrics(metrics_post, igraph::vcount(g))
        
        state$t_global <- state$t_global + 1L
        state$t_stage  <- state$t_stage + 1L
        
        # Eligible set (for transparency); if eligibility throws, default to all
        E_seed <- tryCatch(eligible_vertices(g_seed_pre, stage),
                           error=function(e) seq_len(igraph::vcount(g_seed_pre)))
        
        sel_stub <- list(
          level="seed", metric=NA, rule=NA,
          params=list(),
          eligible_ids=E_seed,
          selected_ids=seeded_ids,
          selected_keys=vertex_key(g_seed_pre, seeded_ids),  # <-- log keys from pre-seed graph
          selected_values=NA_real_
        )
        
        eff <- list(
          mode="seed",
          removed=list(ids=character(0), count=0L),
          infected=list(new_ids=vertex_key(g_seed_pre, seeded_ids),  # <-- from pre-seed graph
                        new_count=length(seeded_ids),
                        total=sum(igraph::V(g)$infected)),
          notes=list()
        )
        
        rr <- make_round_record(state$t_global, si, stage$id, state$t_stage,
                                g_pre = g_seed_pre, g_post = g,   # <-- correct pre graph
                                metrics_pre = metrics_pre,
                                metrics_post = metrics_post,
                                selection = sel_stub,
                                effect = eff)
        
        traj$rounds[[length(traj$rounds)+1]] <- rr
        if (store_graphs) traj$graphs[[length(traj$graphs)+1]] <- g
      }
    }
    
    # Round loop
    repeat {
      # Stop by rounds (checked at top)
      if (stage$loop$type == "rounds" && state$t_stage >= stage$loop$max_rounds) break
      
      # Pre-metrics (drives selection and is logged)
      metrics_pre <- scoring_fun(g, state)
      validate_metrics(metrics_pre, igraph::vcount(g))
      
      # Selection (may be empty for spread-only stages)
      sel <- select_vertices(g, metrics_pre, stage)
      
      # safeguard against hang
      if (stage$mode == "removal" && length(sel$selected_ids) == 0) {
        stop("No vertices selected for removal this round. Check stage$selection (metric/rule/tau) to avoid infinite loop.")
      }
      
      # Apply mechanism
      g_pre <- g
      if (stage$mode == "removal") {
        rem <- apply_removal(g, sel)
        g <- rem$g
        removed_vids <- rem$removed_vids
        eff <- list(
          mode="removal",
          removed=list(ids=vertex_key(g_pre, removed_vids), count=length(removed_vids)),
          infected=list(new_ids=character(0), new_count=0L, total=0L),
          notes=list()
        )
        
      } else if (stage$mode == "infection") {
        upd <- apply_infection(g, stage)
        g <- upd$g
        eff <- list(
          mode="infection",
          removed=list(ids=character(0), count=0L),
          infected=list(new_ids=vertex_key(g_pre, upd$newly_ids),
                        new_count=length(upd$newly_ids),
                        total=upd$infected_total),
          notes=list()
        )
        
      } else if (stage$mode == "infection_removal") {
        upd <- apply_infection_removal(g, stage)
        g <- upd$g
        eff <- list(
          mode="infection_removal",
          removed=list(ids=vertex_key(g_pre, upd$removed_vids), count=length(upd$removed_vids)),
          infected=list(new_ids=vertex_key(g_pre, upd$newly_ids),
                        new_count=length(upd$newly_ids),
                        total=upd$infected_total),
          notes=list()
        )
        
      } else stop("Unknown stage mode")
      
      # Post-metrics (observes perturbed graph)
      metrics_post <- scoring_fun(g, state)
      validate_metrics(metrics_post, igraph::vcount(g))
      
      # Update counters
      state$t_global <- state$t_global + 1L
      state$t_stage  <- state$t_stage + 1L
      
      # Record selection details (metric values from metrics_pre)
      sel_rec <- stage$selection %||% list(level=NA, metric=NA, rule=NA, tau=NA, n=NA, pct=NA)
      selection_rec <- list(
        level = sel_rec$level,
        metric = sel_rec$metric,
        rule = sel_rec$rule,
        params = list(n=sel_rec$n %||% NA_integer_,
                      pct=sel_rec$pct %||% NA_real_,
                      tau=sel_rec$tau %||% NA_real_),
        eligible_ids = sel$eligible_ids,
        selected_ids = sel$selected_ids,
        selected_keys = vertex_key(g_pre, sel$selected_ids),
        selected_values = sel$selected_values
      )
      
      rr <- make_round_record(state$t_global, si, stage$id, state$t_stage,
                              g_pre = g_pre, g_post = g,
                              metrics_pre = metrics_pre,
                              metrics_post = metrics_post,
                              selection = selection_rec,
                              effect = eff)
      
      traj$rounds[[length(traj$rounds)+1]] <- rr
      if (store_graphs) traj$graphs[[length(traj$graphs)+1]] <- g
      
      # Stop conditions (evaluate on metrics_post by default)
      if (igraph::vcount(g) == 0) break
      if (length(sel$eligible_ids) == 0) break
      if (stage$loop$type == "until" &&
          !is.null(stage$loop$safety_max_rounds) &&
          state$t_stage >= stage$loop$safety_max_rounds) break
      if (stage$loop$type == "until") {
        if (isTRUE(stage$loop$until_fun(state, metrics_post, metrics_pre))) break
      }
    }
  }
  
  traj
}




summarize_trajectory <- function(traj) {
  rr <- traj$rounds
  if (length(rr) == 0) return(data.frame())
  
  rows <- lapply(rr, function(x) {
    data.frame(
      t_global = x$t_global,
      stage_index = x$stage$index,
      stage_id = x$stage$id,
      t_stage = x$stage$t_stage,
      n_pre = x$graph$n_pre,
      m_pre = x$graph$m_pre,
      n_post = x$graph$n_post,
      m_post = x$graph$m_post,
      mode = x$effect$mode,
      removed_count = x$effect$removed$count %||% 0L,
      infected_new_count = x$effect$infected$new_count %||% 0L,
      infected_total = x$effect$infected$total %||% 0L,
      stringsAsFactors = FALSE
    )
  })
  
  out <- do.call(rbind, rows)
  rownames(out) <- NULL
  out
}


# ---- metric extraction helpers ----

.extract_round_metric <- function(r, when = c("post","pre"), level, metric) {
  when <- match.arg(when)
  m <- r$metrics[[when]][[level]][[metric]]
  if (is.null(m)) return(NULL)
  m
}

# Returns:
# - scalar metrics: data.frame(round=..., value=...)
# - vector metrics: data.frame(round=..., value=..., mean=...)  (long format)
extract_metric_from_traj <- function(traj, metric, level = c("graph","meso","node"),
                                     when = c("post","pre"),
                                     rounds = NULL,
                                     drop_na = TRUE) {
  level <- match.arg(level)
  when  <- match.arg(when)
  
  rr <- traj$rounds
  if (length(rr) == 0) stop("traj$rounds is empty.")
  
  idx <- seq_along(rr)
  if (!is.null(rounds)) idx <- intersect(idx, rounds)
  
  vals <- lapply(idx, function(i) .extract_round_metric(rr[[i]], when, level, metric))
  
  # identify first non-null to infer type
  first_nonnull <- NULL
  for (v in vals) { if (!is.null(v)) { first_nonnull <- v; break } }
  if (is.null(first_nonnull)) {
    stop(sprintf("Metric '%s' not found in metrics$%s$%s across selected rounds.",
                 metric, when, level))
  }
  
  # scalar series
  if (length(first_nonnull) == 1) {
    out <- data.frame(
      round = idx,
      value = vapply(vals, function(v) if (is.null(v)) NA_real_ else as.numeric(v)[1], numeric(1)),
      stringsAsFactors = FALSE
    )
    if (drop_na) out <- out[!is.na(out$value), , drop = FALSE]
    attr(out, "metric_type") <- "scalar"
    attr(out, "level") <- level
    attr(out, "metric") <- metric
    attr(out, "when") <- when
    return(out)
  }
  
  # vector series (node/meso vectors typically)
  out_list <- lapply(seq_along(idx), function(j) {
    i <- idx[j]
    v <- vals[[j]]
    if (is.null(v)) return(NULL)
    v <- as.numeric(v)
    if (drop_na) v <- v[!is.na(v)]
    if (length(v) == 0) return(NULL)
    data.frame(round = i, value = v, stringsAsFactors = FALSE)
  })
  out <- do.call(rbind, out_list)
  if (is.null(out) || nrow(out) == 0) stop("Metric exists but no values remained after NA filtering.")
  
  # mean trajectory per round
  means <- aggregate(value ~ round, out, mean)
  names(means)[2] <- "mean"
  out <- merge(out, means, by = "round", all.x = TRUE, sort = TRUE)
  
  attr(out, "metric_type") <- "vector"
  attr(out, "level") <- level
  attr(out, "metric") <- metric
  attr(out, "when") <- when
  out
}


# Plot: recorded metric over rounds
plot_metric_over_rounds <- function(traj, metric,
                                    level = c("graph","meso","node"),
                                    when = c("post","pre"),
                                    rounds = NULL,
                                    bins = 30,
                                    ridge_scale = 1.2,
                                    alpha = 0.7,
                                    title = NULL,
                                    subtitle = NULL) {
  
  level <- match.arg(level)
  when  <- match.arg(when)
  
  df <- extract_metric_from_traj(traj, metric = metric, level = level, when = when, rounds = rounds)
  mtype <- attr(df, "metric_type")
  
  # common theme
  base_theme <- ggplot2::theme_minimal(base_size = 12) +
    ggplot2::theme(
      panel.grid.minor = ggplot2::element_blank(),
      plot.title.position = "plot"
    )
  
  if (is.null(title)) {
    title <- sprintf("%s metric over rounds (%s/%s)", metric, when, level)
  }
  
  if (mtype == "scalar") {
    p <- ggplot2::ggplot(df, ggplot2::aes(x = round, y = value)) +
      ggplot2::geom_line(linewidth = 1.1, color = "#2C7FB8") +
      ggplot2::geom_point(size = 2.2, color = "#2C7FB8") +
      ggplot2::labs(x = "Round", y = metric, title = title, subtitle = subtitle) +
      base_theme
    return(p)
  }
  
  # vector metric: ridgeline histograms centered at each round + mean trajectory line.
  # ggridges supports histogram ridgelines via stat="binline" / stat_binline 
  
  # vector metric: density ridges over time, with Round on x-axis (consistent)
  if (requireNamespace("ggridges", quietly = TRUE)) {
    
    # round order left->right
    df$round_f <- factor(df$round, levels = sort(unique(df$round), decreasing = FALSE))
    
    # summary stats per round
    means   <- aggregate(value ~ round, df, mean)
    medians <- aggregate(value ~ round, df, stats::median)
    
    means$round_f   <- factor(means$round, levels = levels(df$round_f))
    medians$round_f <- factor(medians$round, levels = levels(df$round_f))
    
    # clamp to observed range to avoid "impossible" values on bounded metrics
    rng <- range(df$value, na.rm = TRUE)
    
    p <- ggplot2::ggplot(df, ggplot2::aes(x = value, y = round_f)) +
      
      # Use default stat_density_ridges; pass from/to to truncate density grid. [3](https://wilkelab.org/ggridges/reference/stat_density_ridges.html)[4](https://www.rdocumentation.org/packages/ggridges/versions/0.5.7/topics/stat_density_ridges)
      # Negative scale mirrors ridges to the "left" after coord_flip.
      ggridges::geom_density_ridges(
        from = rng[1], to = rng[2],      # truncate density evaluation range [3](https://wilkelab.org/ggridges/reference/stat_density_ridges.html)[4](https://www.rdocumentation.org/packages/ggridges/versions/0.5.7/topics/stat_density_ridges)
        scale = -abs(ridge_scale),       # mirror ridges to left
        alpha = alpha,
        color = "grey30",
        linewidth = 0.25,
        rel_min_height = 0.01
      ) +
      
      # Mean (solid, black) + legend
      ggplot2::geom_path(
        data = means,
        ggplot2::aes(x = value, y = round_f, color = "Mean", linetype = "Mean", group = 1),
        inherit.aes = FALSE,
        linewidth = 0.9
      ) +
      ggplot2::geom_point(
        data = means,
        ggplot2::aes(x = value, y = round_f, color = "Mean"),
        inherit.aes = FALSE,
        size = 1.6
      ) +
      
      # Median (dashed, blue) + legend
      ggplot2::geom_path(
        data = medians,
        ggplot2::aes(x = value, y = round_f, color = "Median", linetype = "Median", group = 1),
        inherit.aes = FALSE,
        linewidth = 0.9
      ) +
      ggplot2::geom_point(
        data = medians,
        ggplot2::aes(x = value, y = round_f, color = "Median"),
        inherit.aes = FALSE,
        size = 1.4
      ) +
      
      # Flip so Round is on x-axis, metric values on y-axis (consistent with your other plots)
      # xlim clamps the *pre-flip* x (i.e., metric values), reinforcing the truncation visually.
      ggplot2::coord_flip(xlim = rng, clip = "off") +
      
      ggplot2::labs(
        x = metric,
        y = "Rounds",
        title = title,
        subtitle = subtitle,
        color = NULL,
        linetype = NULL
      ) +
      
      ggplot2::scale_color_manual(values = c("Mean" = "#900000", "Median" = "#2C7FB8")) +
      ggplot2::scale_linetype_manual(values = c("Mean" = "solid", "Median" = "dashed")) +
      
      base_theme +
      ggridges::theme_ridges(grid = TRUE, center_axis_labels = TRUE) +
      ggplot2::theme(legend.position = "top")
    
    return(p)
  }
  
  
}


# Plot: Infection summary dynamics
plot_infection_dynamics <- function(traj,
                                    title = "Infection dynamics over rounds",
                                    subtitle = NULL,
                                    caption = NULL,
                                    xlab = "Round",
                                    alpha_bars = 0.5,
                                    
                                    # show top label every k rounds (default = 2 -> every other round)
                                    top_label_every = 2,
                                    top_label_start = 1,          # 1 = rounds 1,3,5... ; 2 = rounds 2,4,6...
                                    
                                    top_label_size = 3.0,
                                    top_label_lineheight = 0.95,
                                    segment_label_size = 3.0,
                                    
                                    palette = c(
                                      "Infected (existing)" = "#D7301F",
                                      "New infections"      = "#FC8D59",
                                      "Not infected"        = "#BDBDBD"
                                    ),
                                    line_color = "#2C7FB8",
                                    
                                    # ✅ default segment labels to black for contrast; user can override
                                    segment_label_color = "black",
                                    
                                    # top label color remains customizable
                                    top_label_color = "#333333") {
  
  rr <- traj$rounds
  if (length(rr) == 0) stop("traj$rounds is empty.")
  
  get_num1 <- function(x, default = NA_real_) {
    if (is.null(x)) return(default)
    as.numeric(x)[1]
  }
  
  df <- data.frame(
    round = seq_along(rr),
    n_post = vapply(rr, function(r) get_num1(r$graph$n_post, NA_real_), numeric(1)),
    infected_total = vapply(rr, function(r) get_num1(r$effect$infected$total, 0), numeric(1)),
    new_infections = vapply(rr, function(r) get_num1(r$effect$infected$new_count, 0), numeric(1)),
    stringsAsFactors = FALSE
  )
  
  df <- df[!is.na(df$n_post) & df$n_post >= 0, , drop = FALSE]
  if (nrow(df) == 0) stop("No usable rounds (n_post missing/invalid).")
  
  # integrity guards (keep stacks summing to population)
  df$infected_total <- pmin(pmax(df$infected_total, 0), df$n_post)
  df$new_infections <- pmin(pmax(df$new_infections, 0), df$infected_total)
  
  df$infected_existing <- pmax(df$infected_total - df$new_infections, 0)
  df$not_infected <- pmax(df$n_post - df$infected_total, 0)
  
  df$pct_infected <- ifelse(df$n_post > 0, df$infected_total / df$n_post, NA_real_)
  
  # percent formatting
  if (requireNamespace("scales", quietly = TRUE)) {
    pct_txt <- scales::percent(df$pct_infected, accuracy = 1)
  } else {
    pct_txt <- paste0(round(100 * df$pct_infected), "%")
  }
  
  # two-line top label: "<N> infections\n(XX%)" (newline supported in ggplot labels) 
  df$top_label <- paste0(format(round(df$infected_total), big.mark = ","), "\n(", pct_txt, ")")
  
  # reshape long for stacked bars
  df_long <- rbind(
    data.frame(round = df$round, segment = "Infected (existing)", value = df$infected_existing),
    data.frame(round = df$round, segment = "New infections",      value = df$new_infections),
    data.frame(round = df$round, segment = "Not infected",        value = df$not_infected)
  )
  df_long$segment <- factor(df_long$segment,
                            levels = c("Not infected", "New infections", "Infected (existing)"))
  df_long$label <- ifelse(df_long$value > 0, format(round(df_long$value), big.mark = ","), "")
  
  # ---- show top labels every other round (or every k rounds) by subsetting label data
  top_label_every <- as.integer(top_label_every)
  top_label_start <- as.integer(top_label_start)
  if (is.na(top_label_every) || top_label_every < 1) top_label_every <- 2
  if (is.na(top_label_start) || top_label_start < 1) top_label_start <- 1
  
  df_top <- df[df$round %% top_label_every == (top_label_start %% top_label_every), , drop = FALSE]
  
  # offset above bars for top labels
  y_offset <- 0.025 * max(df$n_post, na.rm = TRUE)
  
  p <- ggplot2::ggplot() +
    ggplot2::geom_col(
      data = df_long,
      ggplot2::aes(x = round, y = value, fill = segment),
      alpha = alpha_bars,
      width = 0.85,
      color = "white",
      linewidth = 0.2
    ) +
    
    # segment labels centered in each stack using position_stack(vjust=0.5) 
    ggplot2::geom_text(
      data = df_long,
      ggplot2::aes(x = round, y = value, label = label, group = segment),
      position = ggplot2::position_stack(vjust = 0.5),
      size = segment_label_size,
      color = segment_label_color,
      check_overlap = TRUE
    ) +
    
    # top labels (subsetted -> every other round)
    ggplot2::geom_text(
      data = df_top,
      ggplot2::aes(x = round, y = n_post + y_offset, label = top_label),
      color = top_label_color,
      size = top_label_size,
      lineheight = top_label_lineheight,
      fontface = "plain",
      vjust = 0
    ) +
    
    # infection line: total infected
    ggplot2::geom_line(
      data = df,
      ggplot2::aes(x = round, y = infected_total),
      linewidth = 1.15,
      color = line_color
    ) +
    ggplot2::geom_point(
      data = df,
      ggplot2::aes(x = round, y = infected_total),
      size = 2.0,
      color = line_color
    ) +
    
    ggplot2::scale_fill_manual(values = palette, name = NULL) +
    ggplot2::labs(
      x = xlab,
      y = "Infections",
      title = title,
      subtitle = subtitle,
      caption = caption
    ) +
    ggplot2::coord_cartesian(clip = "off") +
    ggplot2::theme_minimal(base_size = 12) +
    ggplot2::theme(
      plot.title = ggplot2::element_text(hjust = 0.5, face = "bold", size = 14),
      plot.subtitle = ggplot2::element_text(hjust = 0.5, size = 11, color = "grey30"),
      plot.caption = ggplot2::element_text(size = 9, color = "grey35"),
      panel.background = ggplot2::element_rect(fill = "#FAFAFA", color = NA),
      plot.background  = ggplot2::element_rect(fill = "white",  color = NA),
      panel.grid.major.x = ggplot2::element_blank(),
      panel.grid.minor   = ggplot2::element_blank(),
      panel.grid.major.y = ggplot2::element_line(color = "grey85", linewidth = 0.4),
      axis.line  = ggplot2::element_line(color = "grey55", linewidth = 0.35),
      axis.ticks = ggplot2::element_line(color = "grey55"),
      axis.text  = ggplot2::element_text(color = "grey20"),
      axis.title = ggplot2::element_text(face = "bold", color = "grey10"),
      legend.position = "top",
      legend.justification = "center",
      legend.text = ggplot2::element_text(size = 10),
      plot.margin = ggplot2::margin(t = 10, r = 10, b = 10, l = 10)
    )
  
  p
}


# Animation helper ----
plot_graph_trajectory_gif <- function(
    traj,
    layout_fun = igraph::layout_with_fr,
    
    # Node & edge encodings
    node_size_metric = NULL,          # node-level metric name (metrics$pre$node[[...]]); scaled 5..15
    edge_weight_attr = NULL,          # edge attribute name for width; NULL => uniform
    graph_metric_label = NULL,        # graph-level scalar metric name; shown per frame
    
    # Plot text
    title = NULL,
    subtitle = NULL,
    caption = NULL,
    
    # Animation output
    fps = 5,
    width = 800,
    height = 600,
    file = NULL
) {
  
  stopifnot(requireNamespace("ggplot2", quietly = TRUE))
  stopifnot(requireNamespace("gganimate", quietly = TRUE))
  stopifnot(requireNamespace("igraph", quietly = TRUE))
  stopifnot(requireNamespace("grid", quietly = TRUE))
  
  rounds <- traj$rounds
  graphs <- traj$graphs
  
  if (length(rounds) == 0) stop("traj$rounds is empty.")
  if (length(graphs) == 0) stop("traj$graphs is empty. Run attack_graph(..., store_graphs=TRUE).")
  
  n_rounds <- length(rounds)
  
  # ---- Helper: stable vertex key ----
  .get_keys <- function(g) {
    k <- igraph::vertex_attr(g, "key")
    if (!is.null(k)) return(as.character(k))
    
    nm <- igraph::vertex_attr(g, "name")
    if (!is.null(nm)) return(as.character(nm))
    
    uid <- igraph::vertex_attr(g, "uid")
    if (!is.null(uid)) return(as.character(uid))
    
    stop("Graph vertices need a stable identifier attribute: V(g)$key, V(g)$name, or V(g)$uid.")
  }
  
  # ---- Map stored graphs to per-round pre/post ----
  # Preferred convention: graphs[[1]] is initial, then one snapshot per recorded round => length = n_rounds + 1
  has_prepost <- (length(graphs) >= n_rounds + 1)
  if (!has_prepost) {
    warning("traj$graphs does not appear to include an initial snapshot + one per round. Using graphs[[i]] as the frame graph; 'pre' vs 'post' may be approximate.")
  }
  
  get_g_pre  <- function(i) if (has_prepost) graphs[[i]]   else graphs[[i]]
  get_g_post <- function(i) if (has_prepost) graphs[[i+1]] else graphs[[i]]
  
  # ---- Frame plan: all pre frames + final post frame (requirement #3) ----
  frame_plan <- data.frame(
    round = c(seq_len(n_rounds), n_rounds),
    phase = c(rep("pre", n_rounds), "post"),
    frame = seq_len(n_rounds + 1),
    stringsAsFactors = FALSE
  )
  
  # ---- Frozen layout computed once (requirement #1) ----
  g_layout <- get_g_pre(1)
  keys0 <- .get_keys(g_layout)
  lay <- layout_fun(g_layout)
  layout_df <- data.frame(
    key = keys0,
    x = lay[, 1],
    y = lay[, 2],
    stringsAsFactors = FALSE
  )
  
  # ---- Scaling helpers (5..15 nodes, 1..5 edges) ----
  scale_to_range <- function(x, lo, hi) {
    x <- as.numeric(x)
    r <- range(x, na.rm = TRUE)
    if (!is.finite(r[1]) || !is.finite(r[2]) || r[1] == r[2]) return(rep((lo + hi) / 2, length(x)))
    lo + (x - r[1]) * (hi - lo) / (r[2] - r[1])
  }
  
  # Collect all node metric values across pre frames for global scaling
  all_node_vals <- numeric(0)
  if (!is.null(node_size_metric)) {
    for (i in seq_len(n_rounds)) {
      v <- rounds[[i]]$metrics$pre$node[[node_size_metric]]
      if (!is.null(v)) all_node_vals <- c(all_node_vals, as.numeric(v))
    }
  }
  
  # Collect all edge weights across frame graphs for global scaling
  all_edge_w <- numeric(0)
  if (!is.null(edge_weight_attr)) {
    for (fi in seq_len(nrow(frame_plan))) {
      i <- frame_plan$round[fi]
      gfi <- if (frame_plan$phase[fi] == "pre") get_g_pre(i) else get_g_post(i)
      w <- igraph::edge_attr(gfi, edge_weight_attr)
      if (!is.null(w)) all_edge_w <- c(all_edge_w, as.numeric(w))
    }
  }
  
  # ---- Build per-frame node and edge data ----
  node_rows <- list()
  edge_rows <- list()
  anno_rows <- list()
  
  # Node color palette + legend labels (requirement #2 + legend)
  state_levels <- c("Normal", "Will be infected next", "Infected", "Removed next")
  state_colors <- c(
    "Normal" = "grey70",
    "Will be infected next" = "#8EC9FF",
    "Infected" = "#C68642",
    "Removed next" = "#D73027"
  )
  
  # Determine if the network is directed (for arrows/curvature)
  is_dir <- igraph::is_directed(g_layout)
  
  for (fi in seq_len(nrow(frame_plan))) {
    i  <- frame_plan$round[fi]
    ph <- frame_plan$phase[fi]
    
    rr <- rounds[[i]]
    g  <- if (ph == "pre") get_g_pre(i) else get_g_post(i)
    
    keys <- .get_keys(g)
    nV <- length(keys)
    
    
    # --- Next-FRAME preview sets (removed/infected) ---
    # If this frame is the PRE graph of round i, then the next frame is effectively the POST of round i,
    # so preview should use THIS round's effects.
    next_removed_keys  <- character(0)
    next_infected_keys <- character(0)
    
    if (ph == "pre") {
      next_removed_keys  <- rr$effect$removed$ids %||% character(0)
      next_infected_keys <- rr$effect$infected$new_ids %||% character(0)
    }
    
    
    # --- Current infected state from vertex attributes (if present) ---
    inf_now <- igraph::vertex_attr(g, "infected")
    if (is.null(inf_now)) inf_now <- rep(FALSE, nV)
    
    # --- Node state assignment (priority: removed_next > infected_now > will_infect_next > normal) ---
    state <- rep("Normal", nV)
    state[keys %in% next_infected_keys] <- "Will be infected next"
    state[as.logical(inf_now)]          <- "Infected"
    state[keys %in% next_removed_keys]  <- "Removed next"
    state <- factor(state, levels = state_levels)
    
    # --- Node sizes from node metric (requirement #5) ---
    size <- rep(10, nV)
    if (!is.null(node_size_metric)) {
      if (ph == "pre") {
        vals <- rr$metrics$pre$node[[node_size_metric]]
      } else {
        # final post frame: try post metric; fallback to pre
        vals <- rr$metrics$post$node[[node_size_metric]] %||% rr$metrics$pre$node[[node_size_metric]]
      }
      if (!is.null(vals)) {
        # global scaling if possible
        if (length(all_node_vals) > 0) {
          r <- range(all_node_vals, na.rm = TRUE)
          vals <- as.numeric(vals)
          if (is.finite(r[1]) && is.finite(r[2]) && r[1] != r[2]) {
            size <- 5 + (vals - r[1]) * 10 / (r[2] - r[1])
          } else {
            size <- rep(10, nV)
          }
        } else {
          size <- scale_to_range(vals, 5, 15)
        }
      }
    }
    
    nd <- data.frame(
      key = keys,
      state = state,
      size = size,
      frame = fi,
      stringsAsFactors = FALSE
    )
    nd <- merge(nd, layout_df, by = "key", all.x = TRUE)
    node_rows[[fi]] <- nd
    
    # --- Edge dataframe with curvature and optional weights (requirements #6, #7) ---
    if (igraph::ecount(g) > 0) {
      ends <- igraph::ends(g, igraph::E(g), names = FALSE)
      from_key <- keys[ends[, 1]]
      to_key   <- keys[ends[, 2]]
      
      ed <- data.frame(
        from_key = from_key,
        to_key   = to_key,
        frame = fi,
        stringsAsFactors = FALSE
      )
      
      ed$x    <- layout_df$x[match(ed$from_key, layout_df$key)]
      ed$y    <- layout_df$y[match(ed$from_key, layout_df$key)]
      ed$xend <- layout_df$x[match(ed$to_key, layout_df$key)]
      ed$yend <- layout_df$y[match(ed$to_key, layout_df$key)]
      
      # curvature handling: if reciprocal edge exists, use +/- curvature to separate
      base_curv <- if (is_dir) 0.25 else 0
      if (is_dir) {
        pair <- paste(ed$from_key, ed$to_key, sep = "→")
        revp <- paste(ed$to_key, ed$from_key, sep = "→")
        has_rev <- revp %in% pair
        # sign based on lexicographic order to make deterministic split
        sign <- ifelse(ed$from_key < ed$to_key, 1, -1)
        ed$curvature <- ifelse(has_rev, base_curv * sign, base_curv)
      } else {
        ed$curvature <- 0
      }
      
      # edge widths
      if (is.null(edge_weight_attr)) {
        ed$edge_w <- 1
      } else {
        w <- igraph::edge_attr(g, edge_weight_attr)
        if (is.null(w)) {
          ed$edge_w <- 1
        } else {
          w <- as.numeric(w)
          if (length(all_edge_w) > 0) {
            r <- range(all_edge_w, na.rm = TRUE)
            if (is.finite(r[1]) && is.finite(r[2]) && r[1] != r[2]) {
              ed$edge_w <- 1 + (w - r[1]) * 4 / (r[2] - r[1])
            } else {
              ed$edge_w <- rep(1, length(w))
            }
          } else {
            ed$edge_w <- scale_to_range(w, 1, 5)
          }
        }
      }
      
      edge_rows[[fi]] <- ed
    }
    
    # --- Graph-level metric annotation (requirement #8) ---
    if (!is.null(graph_metric_label)) {
      if (ph == "pre") {
        gv <- rr$metrics$pre$graph[[graph_metric_label]]
      } else {
        gv <- rr$metrics$post$graph[[graph_metric_label]] %||% rr$metrics$pre$graph[[graph_metric_label]]
      }
      if (is.null(gv)) gv <- NA_real_
      anno_rows[[fi]] <- data.frame(
        frame = fi,
        label = sprintf("%s: %s", graph_metric_label,
                        ifelse(is.na(gv), "NA", format(round(as.numeric(gv), 3), nsmall = 3))),
        stringsAsFactors = FALSE
      )
    }
  }
  
  node_df <- do.call(rbind, node_rows)
  edge_df <- if (length(edge_rows)) do.call(rbind, edge_rows) else NULL
  anno_df <- if (length(anno_rows)) do.call(rbind, anno_rows) else NULL
  
  # ---- Build plot ----
  arrow_spec <- if (is_dir) grid::arrow(length = grid::unit(2, "mm"), type = "closed") else NULL
  
  p <- ggplot2::ggplot() +
    {
      if (!is.null(edge_df)) ggplot2::geom_curve(
        data = edge_df,
        ggplot2::aes(x = x, y = y, xend = xend, yend = yend,
                     curvature = curvature, linewidth = edge_w),
        arrow = arrow_spec,
        alpha = 0.35,
        color = "grey40",
        show.legend = FALSE
      )
    } +
    ggplot2::geom_point(
      data = node_df,
      ggplot2::aes(x = x, y = y, color = state, size = size),
      alpha = 0.65
    ) +
    ggplot2::scale_color_manual(values = state_colors, drop = FALSE, name = "Node status") +
    ggplot2::scale_size_identity() +
    ggplot2::scale_linewidth_identity() +
    ggplot2::coord_equal() +
    ggplot2::theme_void() +
    ggplot2::theme(
      legend.position = "top",
      plot.title.position = "plot",
      plot.title = ggplot2::element_text(hjust = 0.5, face = "bold"),
      plot.subtitle = ggplot2::element_text(hjust = 0.5),
      plot.caption = ggplot2::element_text(hjust = 0)
    ) +
    ggplot2::labs(
      title = title,
      subtitle = subtitle,
      caption = caption
    )
  
  # graph metric annotation in top-right corner
  if (!is.null(anno_df)) {
    p <- p + ggplot2::geom_label(
      data = anno_df,
      ggplot2::aes(x = Inf, y = Inf, label = label),
      inherit.aes = FALSE,
      hjust = 1.05,
      vjust = 1.2,
      size = 3.5,
      label.size = 0.2,
      fill = "white",
      alpha = 0.8
    )
  }
  
  
  
  p_anim <- p + gganimate::transition_manual(frame)
  
  if (!is.null(file)) {
    gganimate::animate(
      p_anim,
      fps = fps,
      width = width,
      height = height,
      renderer = gganimate::gifski_renderer(file)
    )
    invisible(NULL)
  } else {
    gganimate::animate(
      p_anim,
      fps = fps,
      width = width,
      height = height
    )
  }
  
}