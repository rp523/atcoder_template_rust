use cargo_snippet::snippet;

#[snippet("Flow")]
#[derive(Clone, Copy)]
pub struct Edge {
    pub to: usize,
    pub rev_idx: usize, // index of paired edge at node "to".
    pub cap: i64,       // immutable capacity, s.t. flow <= cap
    pub flow: i64,      // flow can be negative.
    pub cost: i64,      // for min-cost flow
}
#[snippet("Flow")]
#[derive(Clone)]
pub struct Flow {
    pub g: Vec<Vec<Edge>>,
    flow_lb_sum: i64,
    neg_cost_any: bool,
}
#[snippet("Flow")]
impl Flow {
    pub fn new(n: usize) -> Self {
        Self {
            g: vec![vec![]; n + 2],
            flow_lb_sum: 0,
            neg_cost_any: false,
        }
    }
    pub fn add_edge(&mut self, from: usize, to: usize, cap: i64) {
        self.add_cost_edge(from, to, cap, 0);
    }
    pub fn add_flowbound_edge(&mut self, from: usize, to: usize, cap_min: i64, cap_max: i64) {
        self.add_flowbound_cost_edge(from, to, cap_min, cap_max, 0);
    }
    pub fn add_flowbound_cost_edge(
        &mut self,
        from: usize,
        to: usize,
        cap_min: i64,
        cap_max: i64,
        cost: i64,
    ) {
        self.add_cost_edge(from, to, cap_max - cap_min, cost);
        if cap_min > 0 {
            self.flow_lb_sum += cap_min;
            let dummy_src = self.g.len() - 2;
            self.add_cost_edge(dummy_src, to, cap_min, cost);
            let dummy_dst = self.g.len() - 1;
            self.add_cost_edge(from, dummy_dst, cap_min, cost);
        }
    }
    pub fn add_cost_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) {
        let rev_idx = self.g[to].len();
        self.g[from].push(Edge {
            to,
            rev_idx,
            cap,
            flow: 0,
            cost,
        });
        let rev_idx = self.g[from].len() - 1;
        self.g[to].push(Edge {
            to: from,
            rev_idx,
            cap: 0,
            flow: 0,
            cost: -cost,
        });
        if cost < 0 {
            self.neg_cost_any = true;
        }
    }
    fn bfs(g: &[Vec<Edge>], source: usize) -> Vec<Option<usize>> {
        let mut level = vec![None; g.len()];
        level[source] = Some(0);
        let mut que = std::collections::VecDeque::new();
        que.push_back(source);
        while let Some(v) = que.pop_front() {
            let nxt_level = level[v].unwrap() + 1;
            for edge in g[v].iter().copied() {
                if level[edge.to].is_none() && (edge.flow < edge.cap) {
                    level[edge.to] = Some(nxt_level);
                    que.push_back(edge.to);
                }
            }
        }
        level
    }
    fn dfs(
        g: &mut [Vec<Edge>],
        v: usize,
        sink: usize,
        flow: i64,
        search_cnt: &mut [usize],
        level: &[Option<usize>],
    ) -> i64 {
        if v == sink {
            return flow;
        }
        while search_cnt[v] < g[v].len() {
            let (to, rev_idx, remain_capacity) = {
                let edge = g[v][search_cnt[v]];
                (edge.to, edge.rev_idx, edge.cap - edge.flow)
            };
            if let Some(nxt_level) = level[to] {
                if (level[v].unwrap() < nxt_level) && (remain_capacity > 0) {
                    let additional_flow = Self::dfs(
                        g,
                        to,
                        sink,
                        std::cmp::min(flow, remain_capacity),
                        search_cnt,
                        level,
                    );
                    if additional_flow > 0 {
                        g[v][search_cnt[v]].flow += additional_flow;
                        g[to][rev_idx].flow -= additional_flow;
                        return additional_flow;
                    }
                }
            }
            search_cnt[v] += 1;
        }
        0
    }
    pub fn max_flow(&mut self, src: usize, dst: usize) -> Option<i64> {
        if self.flow_lb_sum == 0 {
            return Some(self.max_flow_impl(src, dst));
        }
        let dummy_src = self.g.len() - 2;
        let dummy_dst = self.g.len() - 1;
        // cyclic flow
        self.add_edge(dst, src, 1 << 60);
        if self.max_flow_impl(dummy_src, dummy_dst) != self.flow_lb_sum {
            return None;
        }
        Some(self.max_flow_impl(src, dst))
    }
    pub fn min_cut_split(&self, src: usize) -> Vec<bool> {
        let nm = self.g.len() - 2;
        let mut split = vec![false; nm];
        let mut que = std::collections::VecDeque::new();
        que.push_back(src);
        while let Some(v) = que.pop_front() {
            for e in self.g[v].iter() {
                if e.flow >= e.cap || split[e.to] {
                    continue;
                }
                split[e.to] = true;
                que.push_back(e.to);
            }
        }
        split
    }
    fn max_flow_impl(&mut self, source: usize, sink: usize) -> i64 {
        let inf = 1i64 << 60;
        let mut flow = 0;
        loop {
            let level = Self::bfs(&self.g, source);
            if level[sink].is_none() {
                break;
            }
            let mut search_cnt = vec![0; self.g.len()];
            loop {
                let additional_flow =
                    Self::dfs(&mut self.g, source, sink, inf, &mut search_cnt, &level);
                if additional_flow > 0 {
                    flow += additional_flow;
                } else {
                    break;
                }
            }
        }
        flow
    }
    pub fn min_cost_flow(
        &mut self,
        src: usize,
        dst: usize,
        flow_lb: i64,
        flow_ub: i64,
    ) -> Option<(i64, i64)> {
        if self.flow_lb_sum == 0 {
            return self.min_cost_flow_impl(src, dst, flow_lb, flow_ub);
        }
        let dummy_src = self.g.len() - 2;
        let dummy_dst = self.g.len() - 1;
        // cyclic flow
        self.add_edge(dst, src, 1 << 60);
        let (dcost, _ds_to_dt) =
            self.min_cost_flow_impl(dummy_src, dummy_dst, self.flow_lb_sum, self.flow_lb_sum)?;
        let (cost, s_to_t) = self.min_cost_flow_impl(src, dst, flow_lb, flow_ub)?;
        Some((cost + dcost, s_to_t))
    }
    fn min_cost_flow_impl(
        &mut self,
        src: usize,
        dst: usize,
        flow_lb: i64, // lower bound flow
        flow_ub: i64, // upper bound flow
    ) -> Option<(i64, i64)> {
        if self.neg_cost_any {
            self.min_negcost_flow(src, dst, flow_lb, flow_ub)
        } else {
            self.min_poscost_flow(src, dst, flow_lb)
        }
    }
    fn min_negcost_flow(
        &mut self,
        source: usize,
        sink: usize,
        flow_lb: i64, // lower bound flow
        flow_ub: i64, // upper bound flow
    ) -> Option<(i64, i64)> {
        let mut flow_now = 0;
        let mut min_cost = 0;
        const INF: i64 = 1 << 60;
        let mut dist = vec![INF; self.g.len()];
        let mut prev = vec![None; self.g.len()];
        loop {
            dist[source] = 0;
            let mut update = true;
            while update {
                update = false;
                for (v, to) in self.g.iter().enumerate() {
                    if dist[v] == INF {
                        continue;
                    }
                    for (ei, e) in to.iter().enumerate() {
                        if e.flow >= e.cap {
                            continue;
                        }
                        let nd = dist[v] + e.cost;
                        if dist[e.to] > nd {
                            dist[e.to] = nd;
                            prev[e.to] = Some((v, ei));
                            update = true;
                        }
                    }
                }
            }

            let dist_sink = dist[sink];
            if dist_sink != INF {
                if (flow_now >= flow_lb) && (dist_sink > 0) {
                    break;
                }
                let mut delta_flow = flow_ub - flow_now;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow = std::cmp::min(delta_flow, e.cap - e.flow);
                        v = pv;
                    }
                }
                if delta_flow == 0 {
                    break;
                }
                min_cost += delta_flow * dist_sink;
                flow_now += delta_flow;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }
            } else if flow_now >= flow_lb {
                break;
            } else {
                return None;
            }

            dist.iter_mut().for_each(|x| *x = INF);
            prev.iter_mut().for_each(|x| *x = None);
        }
        Some((min_cost, flow_now))
    }
    fn min_poscost_flow(
        &mut self,
        source: usize,
        sink: usize,
        flow_lb: i64, // lower bound flow;
    ) -> Option<(i64, i64)> {
        let mut flow_now = 0;
        let mut min_cost = 0;
        let mut h = vec![0; self.g.len()];
        const INF: i64 = 1 << 60;
        let mut dist = vec![INF; self.g.len()];
        let mut prev = vec![None; self.g.len()];
        while flow_now < flow_lb {
            let mut que = std::collections::BinaryHeap::new();
            que.push((std::cmp::Reverse(0), source));
            dist[source] = 0;
            while let Some((std::cmp::Reverse(d), v)) = que.pop() {
                if dist[v] != d {
                    continue;
                }
                for (ei, e) in self.g[v].iter().enumerate() {
                    if e.flow >= e.cap {
                        continue;
                    }
                    let nd = d + e.cost + h[v] - h[e.to];
                    if dist[e.to] > nd {
                        dist[e.to] = nd;
                        prev[e.to] = Some((v, ei));
                        que.push((std::cmp::Reverse(nd), e.to));
                    }
                }
            }
            if dist[sink] == INF {
                return None;
            }
            h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                if d != &INF {
                    *h += d
                }
            });
            let mut delta_flow = flow_lb - flow_now;
            {
                let mut v = sink;
                while let Some((pv, pei)) = prev[v] {
                    let e = &self.g[pv][pei];
                    delta_flow = std::cmp::min(delta_flow, e.cap - e.flow);
                    v = pv;
                }
            }
            min_cost += delta_flow * h[sink];
            flow_now += delta_flow;
            {
                let mut v = sink;
                while let Some((pv, pei)) = prev[v] {
                    self.g[pv][pei].flow += delta_flow;
                    let rev_idx = self.g[pv][pei].rev_idx;
                    self.g[v][rev_idx].flow -= delta_flow;
                    v = pv;
                }
            }

            dist.iter_mut().for_each(|dist| *dist = INF);
            prev.iter_mut().for_each(|dist| *dist = None);
        }
        Some((min_cost, flow_now))
    }
    pub fn min_cost_slope(
        &mut self,
        src: usize,
        dst: usize,
        flow_lb: i64, // lower bound flow
        flow_ub: i64, // upper bound flow
    ) -> Vec<(i64, i64)> {
        if self.neg_cost_any {
            self.min_negcost_slope(src, dst, flow_lb, flow_ub)
        } else {
            self.min_poscost_slope(src, dst, flow_lb)
        }
    }
    fn min_negcost_slope(
        &mut self,
        source: usize,
        sink: usize,
        flow_lb: i64, // lower bound flow
        flow_ub: i64, // upper bound flow
    ) -> Vec<(i64, i64)> {
        let mut slope = vec![];
        let mut flow_now = 0;
        let mut min_cost = 0;
        const INF: i64 = 1 << 60;
        let mut dist = vec![INF; self.g.len()];
        let mut prev = vec![None; self.g.len()];
        loop {
            dist[source] = 0;
            let mut update = true;
            while update {
                update = false;
                for (v, to) in self.g.iter().enumerate() {
                    if dist[v] == INF {
                        continue;
                    }
                    for (ei, e) in to.iter().enumerate() {
                        if e.flow >= e.cap {
                            continue;
                        }
                        let nd = dist[v] + e.cost;
                        if dist[e.to] > nd {
                            dist[e.to] = nd;
                            prev[e.to] = Some((v, ei));
                            update = true;
                        }
                    }
                }
            }

            let dist_sink = dist[sink];
            if dist_sink != INF {
                if (flow_now >= flow_lb) && (dist_sink > 0) {
                    break;
                }
                let mut delta_flow = flow_ub - flow_now;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow = std::cmp::min(delta_flow, e.cap - e.flow);
                        v = pv;
                    }
                }
                if delta_flow == 0 {
                    break;
                }
                min_cost += delta_flow * dist_sink;
                flow_now += delta_flow;
                slope.push((min_cost, flow_now));
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }
            } else {
                break;
            }

            dist.iter_mut().for_each(|x| *x = INF);
            prev.iter_mut().for_each(|x| *x = None);
        }
        slope
    }
    fn min_poscost_slope(
        &mut self,
        source: usize,
        sink: usize,
        flow_lb: i64, // lower bound flow;
    ) -> Vec<(i64, i64)> {
        let mut slope = vec![];
        let mut flow_now = 0;
        let mut min_cost = 0;
        let mut h = vec![0; self.g.len()];
        const INF: i64 = 1 << 60;
        let mut dist = vec![INF; self.g.len()];
        let mut prev = vec![None; self.g.len()];
        while flow_now < flow_lb {
            let mut que = std::collections::BinaryHeap::new();
            que.push((std::cmp::Reverse(0), source));
            dist[source] = 0;
            while let Some((std::cmp::Reverse(d), v)) = que.pop() {
                if dist[v] != d {
                    continue;
                }
                for (ei, e) in self.g[v].iter().enumerate() {
                    if e.flow >= e.cap {
                        continue;
                    }
                    let nd = d + e.cost + h[v] - h[e.to];
                    if dist[e.to] > nd {
                        dist[e.to] = nd;
                        prev[e.to] = Some((v, ei));
                        que.push((std::cmp::Reverse(nd), e.to));
                    }
                }
            }
            if dist[sink] == INF {
                break;
            }
            h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                if d != &INF {
                    *h += d
                }
            });
            let mut delta_flow = flow_lb - flow_now;
            {
                let mut v = sink;
                while let Some((pv, pei)) = prev[v] {
                    let e = &self.g[pv][pei];
                    delta_flow = std::cmp::min(delta_flow, e.cap - e.flow);
                    v = pv;
                }
            }
            min_cost += delta_flow * h[sink];
            flow_now += delta_flow;
            slope.push((min_cost, flow_now));
            {
                let mut v = sink;
                while let Some((pv, pei)) = prev[v] {
                    self.g[pv][pei].flow += delta_flow;
                    let rev_idx = self.g[pv][pei].rev_idx;
                    self.g[v][rev_idx].flow -= delta_flow;
                    v = pv;
                }
            }

            dist.iter_mut().for_each(|dist| *dist = INF);
            prev.iter_mut().for_each(|dist| *dist = None);
        }
        slope
    }
}
