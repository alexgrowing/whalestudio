import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

def optU {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) : Option B.ι → Z.Opens :=
  fun o => o.elim B.U B.V

theorem optU_cover {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) : (⨆ o, optU B o) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [TopologicalSpace.Opens.mem_iSup]
  by_cases hx : x ∈ Set.range i
  · obtain ⟨w, rfl⟩ := hx
    have hw := B.cover (show w ∈ (⊤ : W.Opens) from trivial)
    obtain ⟨α, hα⟩ := (TopologicalSpace.Opens.mem_iSup).1 hw
    exact ⟨some α, hα⟩
  · refine ⟨none, ?_⟩
    show x ∈ (B.U : Set Z)
    rw [B.U_eq]
    exact hx

theorem inU_inf_iff (hSL : SiteLaws) {K : Type} [CommRing K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
    {ι : Type} (f : ι → Z.Opens) (S : Finset ι) (T : Thick (smFun Z q)) :
    inU q (S.inf f) T ↔ ∀ o ∈ S, inU q (f o) T := by
  classical
  have hL := hSL K Z Z Z q (𝟙 Z) (𝟙 Z)
  induction S using Finset.induction_on with
  | empty => simpa using hL.2.2.1 T
  | insert o S ho ih =>
    simp only [Finset.inf_insert, hL.2.2.2.1, ih, Finset.mem_insert, forall_eq_or_imp]

theorem capU_eq (hSL : SiteLaws) {K : Type} [CommRing K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
    {ι : Type} [DecidableEq ι] (f : ι → Z.Opens) (S : Finset ι) (hS : S.Nonempty) :
    capU (fun o => inU q (f o)) S = inU q (S.inf f) := by
  funext T
  apply propext
  rw [inU_inf_iff hSL q f S T]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨o, ho⟩ := hS
    exact ⟨⟨o, h o ho⟩, h⟩

theorem capU_pre (hSL : SiteLaws) {K : Type} [CommRing K] {Z Y : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
    (π : Y ⟶ Z) {ι : Type} [DecidableEq ι] (f : ι → Z.Opens) (S : Finset ι) (hS : S.Nonempty) :
    capU (fun o => inU (π ≫ q) (π ⁻¹ᵁ f o)) S = inU (π ≫ q) (π ⁻¹ᵁ S.inf f) := by
  funext T
  apply propext
  have hp := fun V => (hSL K Z Z Y q (𝟙 Z) π).2.2.2.2.1 V T
  have e := congrFun (capU_eq hSL q f S hS) ((smS π rfl).G.obj T)
  rw [hp, ← e]
  simp only [capU, hp]

theorem relInj_loc (hSL : SiteLaws) (hIso : IsoBij) (hCL : ChartLaws) (hCB : ChartBij)
    (K : Type) [Field K] [CharZero K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) [IsProper q]
    (i : W ⟶ Z) (π : Y ⟶ Z) (D : E.LineData Y) (d : ℕ) (hd : 0 < d) (B : Blow q i π D d) [DecidableEq (Option B.ι)]
    (hQ : Cosieve (On q i)) (hQ' : Cosieve (On (π ≫ q) (pullback.snd i π))) (S : Finset (Option B.ι)) (hS : S.Nonempty)
    (a : ℕ)
    (h : ∀ T, capU (fun o => inU (π ≫ q) (π ⁻¹ᵁ optU B o)) S T →
      capU (fun o => inU q (optU B o)) S ((smS π rfl).G.obj T))
    (h' : ∀ T, On (π ≫ q) (pullback.snd i π) T → On q i ((smS π rfl).G.obj T)) (n : ℕ) :
    Function.Bijective ((pullRC π rfl a (U := capU (fun o => inU q (optU B o)) S)
      (U' := capU (fun o => inU (π ≫ q) (π ⁻¹ᵁ optU B o)) S) hQ hQ' h h').mapH n) := by
  revert h
  rw [capU_eq hSL q (optU B) S hS, capU_pre hSL q π (optU B) S hS]
  intro h
  by_cases hn : none ∈ S
  · exact hIso K Z Y q π B.U (S.inf (optU B)) B.iso (Finset.inf_le (f := optU B) hn) (On q i)
      (On (π ≫ q) (pullback.snd i π)) hQ hQ'
      (fun T hT => ((hSL K W Z Y q i π).2.2.2.2.2 T).2 hT) a h h' n
  · obtain ⟨o, ho⟩ := hS
    obtain ⟨α, rfl⟩ : ∃ α, o = some α := by
      cases o with
      | none => exact absurd ho hn
      | some α => exact ⟨α, rfl⟩
    haveI := B.closed
    haveI : Z.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
    have haff : IsAffineOpen (S.inf (optU B)) := by
      rw [Finset.inf_eq_iInf]
      have := IsAffineOpen.biInf (X := Z) (S : Set (Option B.ι)) S.finite_toSet ⟨_, ho⟩ (U := optU B)
        (fun o' ho' => by
          cases o' with
          | none => exact absurd ho' hn
          | some β => exact (B.c β).affine)
      simpa using this
    obtain ⟨c', -, -⟩ := (hCL K W Z Y q i π d (B.V α) (B.c α)).1 (S.inf (optU B))
      (Finset.inf_le (f := optU B) ho) haff
    exact hCB K W Z Y q i π d hd (S.inf (optU B)) ⟨c'⟩ hQ hQ' a h h' n

end CrystallineSemistableComparison.Onto

end
