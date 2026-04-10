import Mathlib.tactic

import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs
import Filter.MISC

namespace Bourbaki


def _root_.FilterBasis.map {X : Type u} {Y : Type v} (B : FilterBasis X) (f : X → Y) :
  FilterBasis Y
where
  sets := (fun s => f '' s) '' B.sets
  nonempty := by
    use f '' B.nonempty.some; simp only [Set.mem_image, FilterBasis.mem_sets]
    use B.nonempty.some; simp only [and_true]
    exact B.nonempty.some_mem
  inter_sets := by
    intro x y Hx Hy
    simp only [Set.mem_image, FilterBasis.mem_sets, Set.subset_inter_iff, exists_exists_and_eq_and,
      Set.image_subset_iff] at Hx Hy ⊢
    rcases Hx with ⟨x', Bx, rfl⟩
    rcases Hy with ⟨y', By, rfl⟩
    have ⟨z, Bz, Hz⟩ := B.inter_sets Bx By
    use z, Bz
    constructor<;> intro i Hi<;> simp only [Set.mem_preimage, Set.mem_image]<;>
    use i<;> grind


lemma _root_.FilterBasis.map_mono {X : Type u} {Y : Type v} (B C : FilterBasis X) (f : X → Y) :
  B.filter ≤ C.filter → (B.map f).filter ≤ (C.map f).filter
:= by
  intro H s Hs
  rw [FilterBasis.mem_filter_iff] at Hs ⊢
  rcases Hs with ⟨s', Hs', ss⟩
  simp only [FilterBasis.map] at Hs'
  change s' ∈ (fun s ↦ f '' s) '' C.sets at Hs'
  rw [Set.mem_image] at Hs'
  rcases Hs' with ⟨t, Ct, rfl⟩
  have : t ∈ C.filter := by {
    rw [FilterBasis.mem_filter_iff]; use t, Ct
  }
  apply H at this
  rw [FilterBasis.mem_filter_iff] at this
  rcases this with ⟨b, Hb, bt⟩
  use f '' b; constructor
  · simp only [FilterBasis.map]
    change f '' b ∈ (fun s ↦ f '' s) '' B.sets
    simp only [Set.mem_image, FilterBasis.mem_sets]
    use b
  · intro i Hi; simp only [Set.mem_image] at Hi
    apply ss; simp only [Set.mem_image]
    rcases Hi with ⟨j, Hj, rfl⟩
    use j; simp only [and_true]
    apply bt Hj

example {X : Type u} {Y : Type v} (B : FilterBasis X) (f : X → Y) :
  (B.map f).filter = B.filter.map f
:= by
  ext s; simp only [Filter.mem_map, FilterBasis.filter]
  change s ∈ {s | ∃ t ∈ B.map f, t ⊆ s} ↔ f ⁻¹' s ∈ {s | ∃ t ∈ B, t ⊆ s}
  simp only [Set.mem_setOf_eq, FilterBasis.map]
  change(∃ t ∈ (fun s ↦ f '' s) '' B.sets, t ⊆ s) ↔ _
  simp

#check Ultrafilter.map
example {X : Type u} {Y : Type v} (F : Ultrafilter X) (f : X → Y) :
  Ultrafilter Y
:= by
  apply Ultrafilter.ofComplNotMemIff (F.toFilter.map f)
  intro s;  constructor<;> intro Hs
  · simp only [Filter.mem_map, Ultrafilter.mem_coe] at Hs ⊢
    rw [<- F.compl_notMem_iff]
    intro H; apply Hs
    apply F.mem_of_superset H
    intro i Hi
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.preimage_compl] at Hi ⊢
    exact Hi
  · simp only [Filter.mem_map, Ultrafilter.mem_coe] at Hs ⊢
    rw [<- F.compl_notMem_iff] at Hs
    intro H; apply Hs
    apply F.mem_of_superset H
    intro i Hi
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.preimage_compl] at Hi ⊢
    exact Hi



-- ss6-6 命題10
#check Filter.HasBasis.to_image_id
example {X : Type u} {Y : Type v}
  (F : Ultrafilter X) (f : X → Y) (B : Set (Set X)) (HB : F.isBasis B) :
    (F.map f).isBasis ((fun s => f '' s) '' B)
:= by
  rw [F.isBasis_iff] at HB
  unfold Filter.isBasis
  constructor; intro s; simp only [Ultrafilter.coe_map, Filter.mem_map, Ultrafilter.mem_coe,
    Set.mem_image, id_eq, exists_exists_and_eq_and, Set.image_subset_iff]
  simp only [Ultrafilter.mem_coe, id_eq] at HB
  rw [HB]




example {X : Type u} {X' : Type v} (f : X → X') (B' : FilterBasis X') : --(H : ∀ M ∈ B', f ⁻¹' M ≠ ∅) :
  (B'.filter.comap f).isBasis ((fun b => f ⁻¹' b) '' B'.sets)
:= by
  rw [Filter.isBasis_iff]
  intro s;
  simp only [Filter.mem_comap, Set.mem_image, FilterBasis.mem_sets, id_eq, exists_exists_and_eq_and]
  simp only [FilterBasis.filter, Filter.mem_mk, Set.mem_setOf_eq]
  constructor<;> intro Hs
  · rcases Hs with ⟨t, ⟨t', Ht', tt⟩, ts⟩
    use t', Ht'
    intro i Hi; simp only [Set.mem_preimage] at Hi
    apply ts; simp only [Set.mem_preimage]
    apply tt
    exact Hi
  · rcases Hs with ⟨t, Ht, ts⟩
    use t, ?_, ts
    use t


example {X : Type u} {X' : Type v} (f : X → X') (B' : FilterBasis X') :
  (B'.filter.comap f).NeBot ↔  ∀ b ∈ B', f ⁻¹' b ≠ ∅
:= by
  constructor<;> intro H
  · intro b Hb Fb
    apply H.ne; ext s; simp only [Filter.mem_comap, Filter.mem_bot, iff_true]
    use b; rw [Fb]; simp only [Set.empty_subset, and_true]
    unfold FilterBasis.filter
    use b
  · constructor
    intro F
    have : ∅ ∈ Filter.comap f B'.filter := by rw [F]; simp only [Filter.mem_bot]
    simp only [Filter.mem_comap, Set.subset_empty_iff] at this
    rcases this with ⟨b, Hb, Hfb⟩
    rw [FilterBasis.mem_filter_iff] at Hb
    rcases Hb with ⟨b', Bb', bb⟩
    apply H b' Bb'
    ext i; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro Fb; apply bb at Fb
    have : i ∈ f⁻¹' b := by grind
    rw [Hfb] at this; contradiction

end Bourbaki
