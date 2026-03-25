import Mathlib.Order.Filter.Basic
import  Mathlib.Order.Filter.Bases.Finite
-- import Mathlib.Order.Filter.Defs

namespace Bourbaki



/-
Filter.mem_principal (s : Set X) :
  s ∈ Filter.principal t ↔ t ⊆ s
-/

example {X : Type u} {s : Set X} :
  Filter X
where
  sets := { t | s ⊆ t }
  univ_sets := by simp only [Set.mem_setOf_eq, Set.subset_univ]
  inter_sets := by
    simp only [Set.mem_setOf_eq, Set.subset_inter_iff]
    intro x y Hx Hy; exact ⟨Hx, Hy⟩
  sets_of_superset := by
    simp only [Set.mem_setOf_eq]
    intro x y Hx Hy
    exact Hx.trans Hy


/-
Filter.generate_singleton (s : Set X) :
  Filter.generate {s} = Filter.principal s
-/

example {X : Type u} {s : Set X} :
  Filter.generate {s} = Filter.principal s
:= by
  ext x
  rw [Filter.mem_principal]
  constructor<;> intro H
  · induction H with
    | @basic t Ht =>
      simp only [Set.mem_singleton_iff] at Ht
      rw [Ht]
    | univ =>
      simp only [Set.subset_univ]
    | @inter t u Ht Hu IHt IHu =>
      exact Set.subset_inter IHt IHu
    | @superset t u Ht tu IH =>
      exact IH.trans tu
  · rw [Filter.mem_generate_iff]
    use {s}; simp only [subset_refl, Set.finite_singleton, Set.sInter_singleton, true_and]
    exact H


/-
Filter.le_principal_iff.{u} {α : Type u} {s : Set α} {f : Filter α} :
  f ≤ Filter.principal s ↔ s ∈ f
-/

example {X : Type u} {s : Set X} {f : Filter X} :
  f ≤ Filter.principal s ↔ s ∈ f
:= by
  constructor<;> intro H
  · apply H
    rw [Filter.mem_principal]
  · intro x Hx
    rw [Filter.mem_principal] at Hx
    apply f.mem_of_superset H Hx


-- ss6-2 系1
example {X : Type u} (𝓕 : Filter X) (A : Set X) :
  (∃ 𝓕' : Filter X,  A ∈ 𝓕' ∧ 𝓕' ≤ 𝓕 ∧ 𝓕'.NeBot) ↔ (∀ F ∈ 𝓕, F ∩ A ≠ ∅)
:= by
  constructor<;> intro H
  · intro F HF
    rcases H with ⟨𝓕', HA, FF, H𝓕'⟩
    rw [<- Filter.sets_subset_sets] at FF
    apply FF at HF
    have := 𝓕'.inter_sets HF HA
    intro FA; rw [FA] at this
    apply 𝓕'.empty_notMem this
  · use Filter.principal A ⊓ 𝓕
    refine ⟨?_, ?_, ?_⟩
    · apply Filter.mem_inf_of_left
      rw [Filter.mem_principal]
    · apply inf_le_right
    · constructor; intro E
      revert H; simp only [ne_eq, imp_false, not_forall, Decidable.not_not]
      have : ∅ ∈ Filter.principal A ⊓ 𝓕 := by rw [E]; simp only [Filter.mem_bot]
      rw [Filter.mem_inf_iff] at this
      rcases this with ⟨s, Hs, t, Ht, E⟩
      rw [Filter.mem_principal] at Hs
      use t, Ht
      have HA : A = A ∩ s := by exact Set.left_eq_inter.mpr Hs
      rw [HA, Set.inter_comm, Set.inter_assoc, <- E, Set.inter_empty]

end Bourbaki
