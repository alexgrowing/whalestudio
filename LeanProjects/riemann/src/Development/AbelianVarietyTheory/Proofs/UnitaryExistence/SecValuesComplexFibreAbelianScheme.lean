import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_values_complex_fibre : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  intro hT E _ _ _ H Dw l Xo y s
  have hsm : Smooth (gxSnd y) := by
    have := Xo.univ.t.semi.smooth
    exact inferInstanceAs (Smooth (pullback.fst y Xo.univ.t.G.hom))
  have hred : IsReduced (Gx y) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ _ (gxSnd y) hsm).1
  have h1 : ∀ (a : ℂ) i (f : Γ(Gx y, (PPx y).U i)) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) (scal y a i * f) = a * valAt' pt ((PPx y).U i) f := fun a i f pt hp => by
    by_cases h : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i
    · rw [valAt'_mul]
      exact congrArg (· * _) (valAt'_constFn pt (gxSnd y) hp _ a h)
    · rw [valAt'_of_not_le pt h, valAt'_of_not_le pt h, mul_zero]
  have h3 : ∀ i (f g : Γ(Gx y, (PPx y).U i)), (∀ pt : Sp ℂ ⟶ Gx y, pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) f = valAt' pt ((PPx y).U i) g) → f = g := fun i f g h =>
    ComplexPoints.eq_of_valAt'_eq (gxSnd y) _ f g fun pt hp _ => h pt hp
  refine ⟨fun a i pt hp => h1 a i _ pt hp, ⟨fun hs => ?_, ?_⟩, fun s' h i => h3 i _ _ (h i)⟩
  · by_contra hne
    have h0 : ∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s.f i) = 0 := fun i pt hp => by
      by_contra h
      exact hne ⟨i, pt, hp, h⟩
    have hall : ∀ (a : ℂ) i, s.f i = scal y a i * s.f i := fun a i => h3 i _ _ fun pt hp => by
      rw [h1 a i _ pt hp, h0 i pt hp, mul_zero]
    exact zero_ne_one ((hs s).unique (hall 0) (hall 1))
  · rintro ⟨j, q, hq, hv⟩ s'
    obtain ⟨s₀, hs₀⟩ := gfp_gen hT y
    obtain ⟨c, hc, -⟩ := hs₀ s
    have hc0 : c ≠ 0 := fun h => hv (by rw [hc j, h1 c j _ q hq, h, zero_mul])
    obtain ⟨b, hb, hu⟩ := hs₀ s'
    refine ⟨b / c, fun i => h3 i _ _ fun pt hp => ?_, fun a ha => ?_⟩
    · rw [h1 _ i _ pt hp, hb i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, ← mul_assoc, div_mul_cancel₀ _ hc0]
    · rw [eq_div_iff hc0]
      refine hu _ fun i => h3 i _ _ fun pt hp => ?_
      rw [h1 _ i _ pt hp, ha i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, mul_assoc]

end GlobalTheory
