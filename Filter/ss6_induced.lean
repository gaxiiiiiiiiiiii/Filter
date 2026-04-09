import Mathlib.tactic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs

import Filter.MISC

namespace Bourbaki




#print Filter.map
example {X Y : Type u} (m : X → Y) (f : Filter X) :
  Filter Y
where
  sets := Set.preimage m ⁻¹' f.sets
  univ_sets := by
    simp only [Set.mem_preimage, Set.preimage_univ, Filter.mem_sets, Filter.univ_mem]
  inter_sets := by
    intro x y Hx Hy
    simp only [Set.mem_preimage, Filter.mem_sets, Set.preimage_inter,
      Filter.inter_mem_iff] at Hx Hy ⊢
    grind
  sets_of_superset := by
    intro x y Hx H
    simp only [Set.mem_preimage, Filter.mem_sets] at Hx ⊢
    apply f.mem_of_superset Hx
    apply Set.preimage_mono H


#print Filter.comap
example {X Y : Type u} (m : X → Y) (f : Filter Y) :
  Filter X
where
  sets := {s : Set X | ∃ t ∈ f, m ⁻¹' t ⊆ s}
  univ_sets := by
    use Set.univ; simp only [Filter.univ_mem, Set.preimage_univ, subset_refl, and_self]
  inter_sets := by
    intro x y Hx Hy
    simp only [Set.mem_setOf_eq, Set.subset_inter_iff] at Hx Hy ⊢
    rcases Hx with ⟨x', Hx, Ex⟩
    rcases Hy with ⟨y', Hy, Ey⟩
    have Hxy := f.inter_sets Hx Hy
    use x' ∩ y', Hxy; constructor
    · intro i ⟨Hix, Hiy⟩
      apply Ex; simp only [Set.mem_preimage]
      exact Hix
    · intro i ⟨Hix, Hiy⟩
      apply Ey; simp only [Set.mem_preimage]
      exact Hiy
  sets_of_superset := by
    intro x y Hx xy
    simp only [Set.mem_setOf_eq] at Hx ⊢
    rcases Hx with ⟨x', Hx, Ex⟩
    use x', Hx
    exact Ex.trans xy

#check Filter.comap_map
example {X Y : Type u} (m : X → Y) (f : Filter X) (Hm : Function.Injective m) :
  Filter.comap m (Filter.map m f) = f
:= by
  ext x; simp only [Filter.mem_comap, Filter.mem_map]
  constructor<;> intro Hx
  · rcases Hx with ⟨t, Ht, Hxt⟩
    apply f.mem_of_superset Ht Hxt
  · use m '' x
    rw [Hm.preimage_image]
    use Hx

#check Filter.map_neBot
example {X Y : Type u} (m : X → Y) (f : Filter X) (Hf : f.NeBot) :
  (Filter.map m f).NeBot
:= by
  constructor; intro E
  have : ∅ ∈ Filter.map m f := by rw [E]; simp only [Filter.mem_bot]
  simp only [Filter.empty_notMem] at this








-- ss6-5 定義5
abbrev _root_.Filter.induced {X : Type u} (F : Filter X) (A : Set X) : Filter A :=
  Filter.comap Subtype.val F

-- ss6-5 命題8
example {X : Type u} (F : Filter X) (A : Set X) :
  (F.induced A).NeBot ↔ (∀ f ∈ F, f ∩ A ≠ ∅)
:= by
  constructor<;> intro H
  · intro f Hf E
    apply H.ne; ext a; simp only [Filter.mem_comap, Filter.mem_bot, iff_true]
    use f, Hf
    intro i Hi; simp only [Set.mem_preimage] at Hi
    have : i.val ∈ f ∩ A := by grind
    grind
  · constructor; intro E
    have : ∅ ∈ F.induced A := by rw [E]; simp only [Filter.mem_bot]
    simp only [Filter.mem_comap, Set.subset_empty_iff] at this
    rcases this with ⟨f, Hf, Hfx⟩
    apply H f Hf
    ext a; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro fa Aa
    have : ⟨a, Aa⟩ ∈ Subtype.val ⁻¹' f := by grind
    grind

example {X : Type u} (F : Filter X) (A : Set X) (B : Set (Set X)) (HB : F.isBasis B) :
  (F.induced A).isBasis {a : Set A | ∃ b ∈ B, Subtype.val ⁻¹' b ⊆ a}
:= by
  rw [Filter.isBasis_iff]
  intro a
  constructor<;> intro H
  · simp only [Filter.mem_comap] at H
    rcases H with ⟨f, Hf, Hfx⟩
    simp only [Set.mem_setOf_eq, id_eq]
    rw [Filter.isBasis_iff] at HB
    rw [HB] at Hf
    rcases Hf with ⟨b, Hb, bf⟩; simp only [id_eq] at bf
    use Subtype.val ⁻¹' f, ?_, Hfx
    use b, Hb
    exact Set.preimage_mono bf
  · simp only [Set.mem_setOf_eq, id_eq] at H
    rcases H with ⟨a', ⟨b, Hb, ba⟩, aa⟩
    simp only [Filter.mem_comap]
    use b, ?_, ba.trans aa
    rw [F.isBasis_iff] at HB
    rw [HB]; simp only [id_eq]
    use b


#check Filter.NeBot.comap_of_range_mem
example {X Y : Type u} (F : Filter Y) (m : X → Y) (HF : F.NeBot) (Hm : Set.range m ∈ F) :
  (Filter.comap m F).NeBot
:= by
  constructor; intro E
  have : ∅ ∈  Filter.comap m F := by rw [E]; simp only [Filter.mem_bot]
  simp only [Filter.mem_comap, Set.subset_empty_iff] at this
  rcases this with ⟨t, Ht, Et⟩
  rw [Set.preimage_eq_empty_iff, Set.disjoint_iff_inter_eq_empty] at Et
  apply Filter.empty_notMem F
  rw [<- Et]
  apply F.inter_mem Ht Hm


#check Ultrafilter.comap
example {α : Type u} {β : Type v} {m : α → β}
  (U : Ultrafilter β) (Hm : Function.Injective m) (HU : Set.range m ∈ U) :
  Ultrafilter α
:= by
  apply Ultrafilter.mk (Filter.comap m U)
  · apply U.neBot'.comap_of_range_mem HU
  · intro g Hg H s Hs
    simp only [Filter.mem_comap, Ultrafilter.mem_coe]
    use  m '' s
    rw [Hm.preimage_image]
    simp only [subset_refl, and_true]
    apply U.le_of_le (Filter.map m g)
    · apply Filter.map_neBot
    · intro u Hu; simp only [Filter.mem_map]
      apply H; simp only [Filter.mem_comap, Ultrafilter.mem_coe]
      use u, Hu
    · simp only [Filter.mem_map]
      rw [Hm.preimage_image]
      exact Hs

-- ss6-5 定義9
abbrev Ultrafilter.induced {X : Type u} (U : Ultrafilter X) {A : Set X} (AU : A ∈ U) :
  Ultrafilter A
:= by
  apply U.comap (m := @Subtype.val X A) Subtype.val_injective
  rw [Subtype.range_val_subtype]
  exact AU

end Bourbaki
