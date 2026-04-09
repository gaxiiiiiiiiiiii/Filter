import Mathlib.tactic


abbrev Filter.isBasis {X : Type u} (F : Filter X) (B : Set (Set X)) : Prop :=
  F.HasBasis (· ∈ B) id

lemma Filter.isBasis_iff {X : Type u} (F : Filter X) (B : Set (Set X)) :
  F.isBasis B ↔ ∀ (t : Set X), t ∈ F ↔ ∃ i ∈ B, id i ⊆ t
:= by
  unfold Filter.isBasis
  constructor<;> intro H
  · intro f; rw [H.mem_iff]
  · constructor; grind


