import Mathlib.tactic

namespace Bourbaki




/-
フィルターの生成
inductive Filter.GenerateSets{α : Type u} (g : Set (Set α)) : Set α → Prop
  | basic {α : Type u} {g : Set (Set α)} {s : Set α} :
    s ∈ g → GenerateSets g s
  | univ {α : Type u} {g : Set (Set α)} :
    GenerateSets g Set.univ
  | superset {α : Type u} {g : Set (Set α)} {s t : Set α} :
    GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {α : Type u} {g : Set (Set α)} {s t : Set α} :
    GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

def Filter.generate {X : Type u} (S : Set (Set X)) : Filter X
where
  sets :=  Filter.GenerateSets S
  ...

-/


#check Filter.mem_generate_iff
example {X : Type u} {S : Set (Set X)} {U : Set X} :
  U ∈ Filter.generate S ↔ ∃ t, t ⊆ S ∧ t.Finite ∧ (⋂₀ t) ⊆ U
:= by
  constructor<;> intro H
  · induction H with
    | @basic s Hs =>
      use {s};
        simp only [Set.singleton_subset_iff, Set.finite_singleton, Set.sInter_singleton,
        subset_refl, and_self, and_true]; assumption
    | univ =>
      use ∅; simp
    | @superset s t Hs st IH =>
      rcases IH with ⟨t', St', Ht', t's⟩
      use t', St', Ht'
      apply Set.Subset.trans t's st
    | @inter s t Hs Ht IHs IHt =>
      rcases IHs with ⟨s', Ss', Hs', ss⟩
      rcases IHt with ⟨t', St', Ht', tt⟩
      use s' ∪ t'; constructor<;> try constructor
      · intro x Hx
        rcases Hx with Hx | Hx
        · apply Ss' Hx
        · apply St' Hx
      · exact Set.Finite.union Hs' Ht'
      · rw [Set.sInter_union]
        exact Set.inter_subset_inter ss tt
  · rcases H with ⟨t, St, Ht, Ut⟩
    apply Filter.mem_of_superset _ Ut
    apply Set.Finite.induction_to Ht ∅ (by simp)
    · simp only [Set.sInter_empty, Filter.univ_mem]
    · intro s st Hs
      apply Set.exists_of_ssubset at st
      rcases st with ⟨x, Hx, Fx⟩
      use x, ⟨Hx, Fx⟩; simp only [Set.sInter_insert, Filter.inter_mem_iff]
      use ?_, Hs
      apply  Filter.GenerateSets.basic (St Hx)




-- ss7-2 命題2
-- ブルバキとMathlibでフィルターの定義が違うから主張も若干違うけど、ほぼ同じ内容
#check Filter.generate_neBot_iff
example {X : Type u} {S : Set (Set X)} :
  (Filter.generate S).NeBot ↔ ∀ t, t ⊆ S → t.Finite → (⋂₀ t).Nonempty
:= by
  constructor<;> intro H
  · intro t St Ht
    rw [Set.nonempty_iff_empty_ne]; intro F
    apply (Filter.generate S).empty_notMem
    rw [F]
    apply Set.Finite.induction_to (C := fun t =>⋂₀ t ∈ Filter.generate S) Ht ∅ (by simp) (by simp)
    intro s Hs IH;
    simp only [Set.mem_diff, Set.sInter_insert, Filter.inter_mem_iff]
    apply Set.exists_of_ssubset at Hs
    rcases Hs with ⟨x, Hx, Fx⟩
    use x, ⟨Hx, Fx⟩, ?_, IH
    apply Filter.GenerateSets.basic; apply St Hx
  · constructor; intro F
    rw [<- Filter.empty_mem_iff_bot] at F
    rw [Filter.mem_generate_iff] at F
    rcases F with ⟨t, tS, Ht, H0⟩
    simp only [Set.subset_empty_iff] at H0
    specialize H t tS Ht; rw [H0] at H
    rcases H; contradiction
