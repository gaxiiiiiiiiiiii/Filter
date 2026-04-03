import Mathlib.tactic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Set.Finite.Lemmas

namespace Bourbaki

/-

structure Ultrafilter (α : Type*) extends Filter α where
  /-- An ultrafilter is nontrivial. -/
  protected neBot' : NeBot toFilter
  /-- If `g` is a nontrivial filter that is less than or equal to an ultrafilter, then it is greater
  than or equal to the ultrafilter. -/
  protected le_of_le : ∀ g, Filter.NeBot g → g ≤ toFilter → toFilter ≤ g

-/

-- #check Ultrafilter.exists_le
-- 極大フィルターの存在定理は「位相と論理」でやってるからここではパス
-- example {X : Type u} (F : Filter X) :
  -- ∃ (U : Ultrafilter X), U ≤ F


-- ss6-3 命題5
-- #check Ultrafilter.union_mem_iff
example {X : Type u} (F : Ultrafilter X) (A B : Set X) :
  A ∪ B ∈ F ↔ A ∈ F ∨ B ∈ F
:= by
  constructor<;>intro H
  · by_contra f; simp only [not_or] at f
    let G : Filter X := {
      sets := {M | A ∪ M ∈ F}
      univ_sets := by
        simp only [Ultrafilter.union_mem_iff, Set.mem_setOf_eq]
        right; apply F.univ_sets
      inter_sets := by
        simp only [Ultrafilter.union_mem_iff, Set.mem_setOf_eq]
        intro s t Hs Ht
        rw [Classical.or_iff_not_imp_left] at Hs Ht ⊢
        intro f
        apply F.inter_sets (Hs f) (Ht f)
      sets_of_superset := by
        simp only [Ultrafilter.union_mem_iff, Set.mem_setOf_eq]
        intro s t Hs st
        rw [Classical.or_iff_not_imp_left] at Hs ⊢
        intro f
        apply F.sets_of_superset (Hs f) st
    }
    have HB : B ∈ G := by {
      simp only [Filter.mem_mk, G, Set.mem_setOf_eq]
      exact H
    }
    have HG : G.NeBot := by {
      constructor; intro E
      have HA : A ∈ G := by rw [E]; simp only [Filter.mem_bot]
      simp only [Filter.mem_mk, Set.mem_setOf_eq, G] at HA
      rw [Set.union_self] at HA
      apply f.1 HA
    }
    have GF : G ≤ F := by {
      intro C HC; simp only [Filter.mem_mk, Set.mem_setOf_eq, G]
      apply F.mem_of_superset HC
      simp only [Set.subset_union_right]
    }
    have := F.le_of_le G HG GF
    apply this at HB
    apply f.2 HB
  · rcases H with H | H<;>
    apply F.mem_of_superset H (by simp)



-- #check Ultrafilter.finite_sUnion_mem_iff
-- ss6-4 系
example {X : Type u} (F : Ultrafilter X) (s : Set (Set X)) (Hs : s.Finite) :
  ⋃₀ s ∈ F ↔ ∃ a ∈ s, a ∈ F
:= by
  apply Set.Finite.induction_to Hs ∅ (by simp)
  · simp only [Set.sUnion_empty, Ultrafilter.empty_notMem, Set.mem_empty_iff_false, false_and,
    exists_const]
  · intro t ts IH
    simp only [Set.mem_diff, Set.sUnion_insert, Ultrafilter.union_mem_iff, Set.mem_insert_iff,
      exists_eq_or_imp]
    rw [Set.ssubset_iff_exists] at ts
    rcases ts with ⟨ts, x, Hx, Fx⟩
    use x, ⟨Hx, Fx⟩
    constructor<;> intro H
    · rcases H with H | H
      · left; exact H
      · right; apply IH.mp H
    · rcases H with H | H
      · left; exact H
      · right; apply IH.mpr H



-- Ultrafilter.isAtom (F : Ultrafilter X) : IsAtom F.toFilter
-- Ultrafilter.ofAtom (f : Filter X) (Hf : IsAtom f) : Ultrafilter X
-- IsAtom a = (a ≠ ⊥ ∧ ∀ b < a, b = ⊥)
-- (f : Filter X) が超フィルター ↔ IsAtom f
-- 定義より自明だから証明は省略



--  Ultrafilter.mem_or_compl_mem f s : s ∈ f ∨ sᶜ ∈ f
--  Ultrafilter.compl_notMem_iff f s : sᶜ ∉ f ↔ s ∈ f
-- Ultrafilter.ofComplNotMemIff f → (∀ (s : Set α), sᶜ ∉ f ↔ s ∈ f) → Ultrafilter α

-- ss6-4 命題6
example {X : Type u} (F : Filter X) :
  IsAtom F ↔ (F.NeBot ∧ ∀ s : Set X, s ∈ F ∨ sᶜ ∈ F)
:= by
  constructor<;> intro H
  · constructor
    · constructor
      exact H.1
    · intro S
      let F' := Ultrafilter.ofAtom F H
      suffices : S ∈ F' ∨ Sᶜ ∈ F'
      · apply this
      · rw [<- F'.union_mem_iff]
        simp only [Set.union_compl_self]
        apply F'.univ_mem
  · rcases H with ⟨H, HF⟩
    use H.ne'
    intro G HG; ext S; simp only [Filter.mem_bot, iff_true]
    rw [lt_iff_le_and_ne] at HG
    rcases HG with ⟨HG, FG⟩
    rcases HF S with HS | FS
    · apply HG HS
    · have GS := HG FS
      by_contra SG
      apply FG; ext T
      constructor<;> intro HT; swap
      · apply HG HT
      · rcases HF T with hT | hT
        · exact hT
        · apply HG at hT
          have := G.inter_sets HT hT
          simp only [Set.inter_compl_self, Filter.mem_sets] at this
          by_contra _; apply SG
          apply G.mem_of_superset this (by simp)


-- ss6-4 命題7
example {X : Type u} (F : Filter X) :
  sSup {G : Filter X | G ≤ F} = F
:= by
  apply le_antisymm
  · apply sSup_le; simp only [Set.mem_setOf_eq, imp_self, implies_true]
  · intro S HS
    simp only [Filter.mem_sSup, Set.mem_setOf_eq] at HS
    apply HS; simp

end Bourbaki
