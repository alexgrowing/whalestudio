import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace P_sumList

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem monomial_sum_iff_alt (x y : WD h) : (WD.lpSum x y).mono0 ↔ x.mono0 ∧ y.mono0 := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
      constructor
      · intro hN
        refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
        · have := congrArg Prod.fst (LinearMap.congr_fun hN (v, 0))
          simpa using this
        · have := congrArg Prod.snd (LinearMap.congr_fun hN (0, v))
          simpa using this
      · rintro ⟨ha, hb⟩
        rw [ha, hb, LinearMap.prodMap_zero]

theorem charPol_lpSum (x y : WD h) (σ : Weil h) :
    (WD.lpSum x y).charPol σ = x.charPol σ * y.charPol σ := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.charPol_mk, WD.charPol_mk, WD.charPol_mk, WDRep.sum_ρ,
        LinearMap.charpoly_prodMap]

theorem monomial_zero_alt : (WD.lpZero h).mono0 := by
  rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.diag_N]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero h).charPol σ = 1 := by
  refine Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ) ?_
  rw [WD.charPol_natDegree, WD.lpZero, WD.lpDim_mk]
  simp

end P_sumList

open P_sumList in
theorem step_sumList : SumOverListProp := by
  intro E Ω _ _ _ _ _ A w h l
  refine ⟨?_, fun σ => ?_⟩
  · induction l with
    | nil => simp [sumList, monomial_zero_alt]
    | cons y l ih =>
      rw [sumList, List.foldr_cons, ← sumList, monomial_sum_iff_alt, ih]
      simp
  · induction l with
    | nil => simp [sumList, charPol_lpZero]
    | cons y l ih =>
      rw [sumList, List.foldr_cons, ← sumList, charPol_lpSum, ih, List.map_cons, List.prod_cons]

end UpperTheory.TNZ
