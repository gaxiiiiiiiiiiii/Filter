import Mathlib.tactic

namespace Bourbaki



/-

Filter.sup_sets_eq f g :
  (f ⊔ g).sets = f.sets ∩ g.sets

Filter.mem_inf_iff f g  :
  s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂

Filter.sSup_sets_eq :
  (sSup s).sets = ⋂ f ∈ s, f.sets

-/

local instance (X : Type u) :
  Min (Filter X)
where
  min F G :=  {
    sets := { s | ∃ t₁ ∈ F, ∃ t₂ ∈ G, s = t₁ ∩ t₂ }
    univ_sets := by
      simp only [Set.mem_setOf_eq]
      use Set.univ, F.univ_sets, Set.univ, G.univ_sets; simp only [Set.inter_self]
    inter_sets := by
      intro s₁ s₂ ⟨f₁, Hf₁, g₁, Hg₁, H₁⟩  ⟨f₂, Hf₂, g₂, Hg₂, H₂⟩
      rw [H₁, H₂]; simp only [Set.mem_setOf_eq]
      use f₁ ∩ f₂, F.inter_sets Hf₁ Hf₂, g₁ ∩ g₂, G.inter_sets Hg₁ Hg₂
      grind
    sets_of_superset := by
      intro s t ⟨f, Hf, g, Hg, Hs⟩ Ht
      simp only [Set.mem_setOf_eq]
      subst s
      have H1 := F.sets_of_superset Hf (y := f ∪ t) (by simp only [Set.subset_union_left])
      have H2 := G.sets_of_superset Hg (y := g ∪ t) (by simp only [Set.subset_union_left])
      use f ∪ t, H1, g ∪ t, H2
      grind
  }

local instance (X : Type u) :
  Max (Filter X)
where
  max F G := {
    sets := F.sets ∩ G.sets
    univ_sets := by
      simp only [Set.mem_inter_iff, Filter.mem_sets, Filter.univ_mem, and_self]
    inter_sets := by
      simp only [Set.mem_inter_iff, Filter.mem_sets, Filter.inter_mem_iff, and_imp]
      intros; grind
    sets_of_superset := by
      simp only [Set.mem_inter_iff, Filter.mem_sets, and_imp]
      intro s t Fs Gs Ht
      use F.sets_of_superset Fs Ht
      apply G.sets_of_superset Gs Ht
  }



local instance Filter.lattice (X : Type u) :
  Lattice (Filter X)
:= by
  apply Lattice.mk'
  · intro F G; ext s;
    simp only [max, Filter.mem_mk, Set.mem_inter_iff, Filter.mem_sets]
    grind
  · intro F G H; ext s
    simp only [max, Filter.mem_mk, Set.mem_inter_iff, Filter.mem_sets]
    grind
  · intro F G; ext s
    simp only [min, Filter.mem_mk, Set.mem_setOf_eq]
    grind
  · intro F G H; ext s
    simp only [min, Filter.mem_mk, Set.mem_setOf_eq]
    grind
  · intro F G; ext s;
    simp only [max, min, Filter.mem_mk, Set.mem_inter_iff, Filter.mem_sets,
    Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro Hs; use s, Hs, Set.univ, G.univ_sets; simp only [Set.inter_univ]
  · intro F G; ext s
    simp only [min, max, Filter.mem_mk, Set.mem_inter_iff, Filter.mem_sets, Set.mem_setOf_eq]
    constructor<;> intro Hs
    · rcases Hs with ⟨f, Ff, g, ⟨Fg, Gg⟩, rfl⟩
      apply F.inter_sets Ff Fg
    · use s, Hs, Set.univ, ⟨F.univ_sets, G.univ_sets⟩; simp


local instance (X : Type u) :
  LE (Filter X)
:= (Filter.lattice X).toSemilatticeSup.toPartialOrder.toPreorder.toLE


lemma le_def {X : Type u} (F G : Filter X) :
  F ≤ G ↔ ∀ s, s ∈ G → s ∈ F
:= by
  rw [<- sup_eq_right]
  constructor<;> intro H
  · intro x Hx; rw [<- H] at Hx
    simp only [max, SemilatticeSup.sup, Filter.mem_mk, Set.mem_inter_iff, Filter.mem_sets] at Hx
    exact Hx.1
  · ext x; simp only [max, SemilatticeSup.sup, Filter.mem_mk, Set.mem_inter_iff, Filter.mem_sets]
    grind




local instance (X : Type u) :
  SupSet (Filter X)
where
  sSup S := {
    sets := ⋂ f ∈ S, f.sets
    univ_sets := by simp only [Set.mem_iInter, Filter.mem_sets, Filter.univ_mem, implies_true]
    inter_sets := by
      simp only [Set.mem_iInter, Filter.mem_sets, Filter.inter_mem_iff]
      intro s t  Hs Ht i Hi; grind
    sets_of_superset := by
      intro s t; simp only [Set.mem_iInter, Filter.mem_sets]
      intro Hs Ht u Hu
      apply u.sets_of_superset (Hs u Hu) Ht
  }


local instance (X : Type u) :
  InfSet (Filter X)
where
  sInf S :=  Filter.generate (⋃ f ∈ S, f.sets)

local instance (X : Type u) :
  PartialOrder (Filter X)
where
  le F G := ∀ s, s ∈ G → s ∈ F
  le_refl := by simp
  le_trans := by grind
  le_antisymm := by
    intro F G Hl Hr; ext s; grind


local instance (X : Type u) :
  BoundedOrder (Filter X)
where
  bot := {
    sets := Set.univ
    univ_sets := by simp
    inter_sets := by simp
    sets_of_superset := by simp
  }
  bot_le := by
    intro F
    rw [le_def]
    intro x Hx; simp
  top := {
    sets := {Set.univ}
    univ_sets := by simp
    inter_sets := by simp
    sets_of_superset := by
      intro x y; simp only [Set.mem_singleton_iff]
      intro rfl; simp
  }
  le_top := by
    intro F
    rw [le_def]
    intro x Hx;
    simp only [Filter.mem_mk, Set.mem_singleton_iff] at Hx
    subst x; apply F.univ_sets


local instance (X : Type u) :
  CompleteLattice (Filter X)
where
  le_sSup := by
    intro S s Hs
    rw [le_def]
    intro x Hx
    simp only [sSup, Filter.mem_mk, Set.mem_iInter, Filter.mem_sets] at Hx
    apply Hx s Hs
  sSup_le := by
    intro S F HF
    rw [le_def]
    intro x Hx
    simp only [sSup, Filter.mem_mk, Set.mem_iInter, Filter.mem_sets]
    intro G HG
    specialize HF G HG
    rw [le_def] at HF
    apply HF x Hx
  sInf_le S F HF := by
    rw [le_def]
    intro x Hx
    simp only [sInf]
    rw [Filter.mem_generate_iff]
    use {x}
    simp only [Set.singleton_subset_iff, Set.mem_iUnion, Filter.mem_sets, exists_prop,
      Set.finite_singleton, Set.sInter_singleton, subset_refl, and_self, and_true]
    use F, HF, Hx
  le_sInf S F HF := by
    rw [le_def]
    intro x Hx; simp only [sInf] at Hx
    induction Hx with
    | @basic x Hx =>
      simp only [Set.mem_iUnion, Filter.mem_sets, exists_prop] at Hx
      rcases Hx with ⟨s, Hs, xs⟩
      specialize HF s Hs
      rw [le_def] at HF
      apply HF x xs
    | univ =>
      apply F.univ_sets
    | @superset s t Hs st IH =>
      apply F.mem_of_superset IH st
    | @inter s t Hs Ht IHs IHt =>
      apply F.inter_sets IHs IHt
















end Bourbaki
