import Mathlib.Order.Filter.Basic
import  Mathlib.Order.Filter.Bases.Finite
import Mathlib.Order.Filter.Defs

namespace Bourbaki

-- FilterBasis
@[ext]
structure Basis (X : Type u) where
  sets : Set (Set X)
  nonempty : sets.Nonempty
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y

def Basis.filter (B : Basis X) : Filter X
where
  sets := { s | ∃ t ∈ B.sets, t ⊆ s }
  univ_sets := by
    simp only [Set.mem_setOf_eq, Set.subset_univ, and_true]
    use B.nonempty.some
    exact Set.Nonempty.some_mem B.nonempty
  inter_sets := by
    intro x y Hx Hy; simp only [Set.mem_setOf_eq, Set.subset_inter_iff] at Hx Hy ⊢
    rcases Hx with ⟨x', Hx', xx⟩
    rcases Hy with ⟨y', Hy', yy⟩
    have ⟨z, Hz, zxy⟩ := B.inter_sets Hx' Hy'
    use z, Hz; grind
  sets_of_superset := by
    intro x y Hx xy; simp only [Set.mem_setOf_eq] at Hx ⊢
    rcases Hx with ⟨x', Hx', xx⟩
    use x', Hx', xx.trans xy

-- FilterBasis.generate
example {X : Type u} (B : FilterBasis X) :
  Filter.generate B.sets = B.filter
:= by
  ext s; rw [FilterBasis.mem_filter_iff]
  constructor<;> intro Hs
  · induction Hs with
    | @basic t Ht =>
      use t, Ht
    | univ =>
      use B.nonempty.some, Set.Nonempty.some_mem B.nonempty
      simp only [Set.subset_univ]
    | @inter t u Ht Hu IHt IHu =>
      rcases IHt with ⟨t', Ht', tt'⟩
      rcases IHu with ⟨u', Hu', uu'⟩
      have ⟨v, Hv, vtu⟩ := B.inter_sets Ht' Hu'
      use v, Hv; grind
    | @superset t u Ht tu IH =>
      rcases IH with ⟨v, Hv, vt⟩
      use v, Hv, vt.trans tu
  · rcases Hs with ⟨t, Ht, ts⟩
    apply Filter.mem_of_superset _ ts
    apply Filter.mem_generate_of_mem Ht

@[ext]
structure IsBasis {X : Type u} (F : Filter X) (B : Set (Set X)) : Prop where
  subset : B ⊆ F.sets
  isBasis : ∀ f ∈ F, ∃ b ∈ B, b ⊆ f

--  ブルバキ流とMathlib流のフィルターの基底の同値性
example {X : Type u} (F : Filter X) (B : Set (Set X)) :
  IsBasis F B ↔ F.HasBasis (· ∈ B) id
:= by
  constructor<;> intro H
  · rcases H with ⟨BF, HB⟩
    constructor; intro f; simp only [id_eq]
    constructor<;> intro Hf
    · exact HB f Hf
    · rcases Hf with ⟨b, Hb, bf⟩
      apply BF at Hb
      apply F.mem_of_superset Hb bf
  · constructor
    · intro x Hx; simp only [Filter.mem_sets]
      rw [H.mem_iff]
      use x, Hx; simp only [id_eq, subset_refl]
    · intro f Hf
      rw [H.mem_iff] at Hf; simp only [id_eq] at Hf
      exact Hf

def IsBasis.basis (F : Filter X) (B : Set (Set X)) (HB : IsBasis F B) : Basis X
where
  sets := B
  nonempty := by
    have ⟨b, Hb, _⟩ := HB.isBasis Set.univ (F.univ_sets)
    use b, Hb
  inter_sets := by
    intro x y Hx Hy
    have Hxy := F.inter_sets (HB.subset Hx) (HB.subset Hy)
    apply HB.isBasis _ Hxy

-- FilterBasis.hasBasis
def Basis.isBasis (X : Type u) (B : Basis X) :
  IsBasis (B.filter) B.sets
where
  subset := by
    intro x Hx; simp only [Filter.mem_sets]
    simp only [filter, Filter.mem_mk, Set.mem_setOf_eq]
    use x, Hx
  isBasis := by
    intro b Hb
    exact Hb


example {X : Type u} (F : Filter X) (B : Set (Set X)) (HB : IsBasis F B) :
   HB.basis.filter = F
:= by
  ext x; simp only [Basis.filter, Filter.mem_mk, Set.mem_setOf_eq, IsBasis.basis]
  constructor<;> intro H
  · rcases H with ⟨b, Hb, bx⟩
    apply HB.subset at Hb
    apply F.mem_of_superset Hb bx
  · apply HB.isBasis _ H

-- ss6-3 命題4
-- Filter.HasBasis.le_basis_iff
example {X : Type u} (B B' : FilterBasis X) :
  B'.filter ≤ B.filter ↔ ∀ b ∈ B, ∃ b' ∈ B', b' ⊆ b
:= by
  constructor<;> intro H
  · intro b Hb
    rw [<- FilterBasis.mem_filter_iff]
    apply H
    rw [FilterBasis.mem_filter_iff]
    use b, Hb
  · intro s Hs
    rw [FilterBasis.mem_filter_iff] at Hs ⊢
    rcases Hs with ⟨b, Hb, bs⟩
    specialize H b Hb
    rcases H with ⟨b', Hb', bb⟩
    use b', Hb', bb.trans bs



end Bourbaki
