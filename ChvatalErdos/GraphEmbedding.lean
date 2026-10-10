import ChvatalErdos.DirectedPaths
import ChvatalErdos.CyclePacking
import Mathlib.Data.Finset.Image

set_option autoImplicit false

namespace ChvatalErdos
variable {V W : Type} {F : Digraph V} {D : Digraph W}

structure GraphEmbedding (F : Digraph V) (D : Digraph W) where
  vertex : V → W
  injective : Function.Injective vertex
  arc : ∀ u v, F.arc u v → D.arc (vertex u) (vertex v)

theorem GraphEmbedding.twoCycle (e : GraphEmbedding F D) {u v : V} (h : TwoCycle F u v) :
    TwoCycle D (e.vertex u) (e.vertex v) := ⟨e.arc u v h.1,e.arc v u h.2⟩

def DPath.mapGraph (P : DPath F) (e : GraphEmbedding F D) : DPath D where
  vertices := P.vertices.map e.vertex
  nonempty := by
    cases hp : P.vertices with
    | nil => exact (P.nonempty hp).elim
    | cons v l => simp
  nodup := P.nodup.map e.injective
  chain := List.isChain_map_of_isChain e.vertex e.arc P.chain

theorem DPath.first_mapGraph (P : DPath F) (e : GraphEmbedding F D) :
    (P.mapGraph e).first = e.vertex P.first := by simp [DPath.first,DPath.mapGraph]

theorem DPath.last_mapGraph (P : DPath F) (e : GraphEmbedding F D) :
    (P.mapGraph e).last = e.vertex P.last := by simp [DPath.last,DPath.mapGraph]

theorem DPath.support_mapGraph [DecidableEq V] [DecidableEq W] (P : DPath F) (e : GraphEmbedding F D) :
    (P.mapGraph e).support = P.support.image e.vertex := by
  ext v
  simp [DPath.support,DPath.mapGraph]

theorem DPath.disjoint_mapGraph [DecidableEq V] [DecidableEq W] (P Q : DPath F)
    (e : GraphEmbedding F D) (hd : Disjoint P.support Q.support) :
    Disjoint (P.mapGraph e).support (Q.mapGraph e).support := by
  rw [P.support_mapGraph,Q.support_mapGraph]
  exact (Finset.disjoint_image e.injective).mpr hd

theorem DPath.arc_mapGraph [DecidableEq V] [DecidableEq W] (P : DPath F) (e : GraphEmbedding F D)
    (u v : V) (h : P.HasArc u v) : (P.mapGraph e).HasArc (e.vertex u) (e.vertex v) := by
  obtain ⟨l,r,hr⟩ := h
  refine ⟨l.map e.vertex,r.map e.vertex,?_⟩
  simp [DPath.mapGraph,hr]

def UPath.mapGraph (P : UPath F) (e : GraphEmbedding F D) : UPath D where
  vertices := P.vertices.map e.vertex
  nonempty := by
    cases hp : P.vertices with
    | nil => exact (P.nonempty hp).elim
    | cons v l => simp
  nodup := P.nodup.map e.injective
  chain := List.isChain_map_of_isChain e.vertex (fun _ _ h => e.twoCycle h) P.chain

theorem UPath.support_mapGraph [DecidableEq V] [DecidableEq W] (P : UPath F) (e : GraphEmbedding F D) :
    (P.mapGraph e).support = P.support.image e.vertex := by
  ext v
  simp [UPath.support,UPath.mapGraph]

def UCycle.mapGraph {b : Nat} (Q : UCycle F b) (e : GraphEmbedding F D) : UCycle D b where
  vertex := fun i => e.vertex (Q.vertex i)
  injective := e.injective.comp Q.injective
  edge i := e.twoCycle (Q.edge i)

theorem UCycle.support_mapGraph [DecidableEq V] [DecidableEq W] {b : Nat} (Q : UCycle F b) (e : GraphEmbedding F D) :
    (Q.mapGraph e).support = Q.support.image e.vertex := by
  simp [UCycle.support,UCycle.mapGraph,Finset.image_image,Function.comp_def]

theorem UPath.first_mapGraph (P : UPath F) (e : GraphEmbedding F D) :
    (P.mapGraph e).first = e.vertex P.first := by simp [UPath.first,UPath.mapGraph]

theorem UPath.last_mapGraph (P : UPath F) (e : GraphEmbedding F D) :
    (P.mapGraph e).last = e.vertex P.last := by simp [UPath.last,UPath.mapGraph]

theorem UPath.disjoint_mapGraph [DecidableEq V] [DecidableEq W] (P Q : UPath F)
    (e : GraphEmbedding F D) (hd : Disjoint P.support Q.support) :
    Disjoint (P.mapGraph e).support (Q.mapGraph e).support := by
  rw [P.support_mapGraph,Q.support_mapGraph]
  exact (Finset.disjoint_image e.injective).mpr hd

end ChvatalErdos

#print axioms ChvatalErdos.DPath.disjoint_mapGraph
#print axioms ChvatalErdos.UCycle.mapGraph
