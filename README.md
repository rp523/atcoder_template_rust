# 実装プラン

HeavyLightDecomposition(g, root=0):rootを根とした重軽分解を構築する。
https://judge.yosupo.jp/problem/vertex_add_path_sum
https://atcoder.jp/contests/abc294/tasks/abc294_g

idx(i): 頂点iのオイラーツアー順をpair(down, up)の形で返す。
path_query(u, v, vertex, f): 可換なパスクエリを処理する。
path_noncommutative_query(u, v, vertex, f): 非可換なパスクエリを処理する。
subtree_query(u, vertex, f): 部分木クエリを処理する。
lca(u, v): uとvの最小共通祖先(LCA)を返す。

member
各ノードの根からの距離
各decomposed_nodeの最小祖先
各decomposed_nodeの派生元decompose
Decompose情報を保持するUnionFind
decomposed_tree。ノード数はNで、ノード番号との対応づけはUnionFindでやる
decomposed_treeのノード間エッジ情報。decomposeしたらノード数はLogNだから、二次元配列でいい



method

初期化（セグ木と同じジェネリック型を要求）
DFSして部分木のサイズを求める
DFSでheavyなchildごとにUnionFindでまとめる。このときにオイラーツアー順と派生元decomposeも生成する
heavyなパスをまとめたDecomposedTreeを構築
decomposed_tree上のノードとエッジにSegtreeを構築

LCA
同じdecomposed_treeに属するなら、その距離の短いほう
違うなら、各decomposed_nodeの最小祖先の距離の長いほうに属するノードを分岐元ノードに移動させる

Path_query（引数は両端ノード）
LCAみつけるのと同じやり方

subtree_query(引数は元の木のノード番号)
