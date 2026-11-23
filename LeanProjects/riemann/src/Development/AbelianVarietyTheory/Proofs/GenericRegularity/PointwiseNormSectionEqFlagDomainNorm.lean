import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Comparison₂

theorem isReduced_cAt {K : Type} [Field K] (σ : K →+* ℂ) : IsReduced (CAt σ) :=
  inferInstanceAs (IsReduced ℂ)

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (z w : CAt σ) : cabs (z * w) = cabs z * cabs w :=
  norm_mul (show ℂ from z) (show ℂ from w)

theorem cabs_wchar {K : Type} [Field K] {σ : K →+* ℂ} {ι : Type} [Fintype ι] (e : ι → ℕ) (t : ι → (CAt σ)ˣ) :
    cabs (wchar e t) = ∏ i, cabs (t i : CAt σ) ^ e i := by
  have h := norm_prod (α := ℂ) Finset.univ (fun i => (show ℂ from (t i : CAt σ)) ^ e i)
  exact h.trans (Finset.prod_congr rfl fun i _ => norm_pow (α := ℂ) _ _)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (u : (CAt σ)ˣ) : 0 < cabs (u : CAt σ) :=
  norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) u)

theorem cabs_conjAlg {K : Type} [Field K] (σ : K →+* ℂ) (z : CAt σ) : cabs (conjAlg σ z) = cabs z :=
  Complex.norm_conj (show ℂ from z)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem baseNorm_pos (Dw : Datum H) {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some p => exact Real.sqrt_pos.2 (by positivity)

theorem prod_baseNorm (Dw : Datum H) {x : ℝ} (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∏ i, (baseNorm Dw x i)⁻¹ ^ ex Dw a n i = Formalism.L2.PjFree.lieFac Dw x a := by
  classical
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hs : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, ← Real.exp_neg]
    congr 1; ring
  rw [Fintype.prod_option]
  simp only [baseNorm, ex, inv_one, one_pow, one_mul, hs, ← Real.exp_nat_mul]
  rw [← Real.exp_sum, Formalism.L2.PjFree.lieFac, ← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_sigma]
  ring

theorem ptNorm_eq_pnorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hP
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ y i, fn σ y i ≠ 0 := by
    intro σ hσ y i
    obtain ⟨k, x, t, hx1, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).2 y
    have h := hP.1 σ hσ k x hx1 t y ht i
    rw [← abs_pos, h]
    exact mul_pos (cabs_unit_pos _) (baseNorm_pos Dw hx i)
  refine ⟨fun σ y i => ?_, fun σ hσ k x t y ht a n hd f hf => ?_, fun σ y y' hm a n f hf => ?_⟩
  · by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · exact hgood σ hσ y i
    · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
        have h := Formalism.L2.PjFree.goodEmb_goodOf c σ
        rwa [Formalism.L2.PjFree.goodOf, if_neg hσ] at h
      obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
      rw [← abs_pos, ← hP.2 σ y y' hy' i, abs_pos]
      exact hgood _ hσ' y' i
  · obtain ⟨x', hx', -, ⟨t', ht'⟩, hpn⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).1 k x
    have htt := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).2.1 t' t _ _ _ ht' ht
    have hfn := hP.1 σ hσ k x' hx' _ y htt
    have hev := hwt (CAt σ) (isReduced_cAt σ) a n f hf _ _ _ htt
    rw [hpn _ _ ((hU σ hσ).2.2.2.2.1 a n hd f hf k)]
    have hrd : ‖Formalism.L2.PjFree.rdU (U σ) f k x'.1‖ = cabs (evR Xo c f ((U σ).un k x')) := by
      have e : Formalism.L2.PjFree.rdU (U σ) f k x'.1 = Formalism.L2.PjFree.toC (evR Xo c f ((U σ).un k x')) :=
        dif_pos x'.2
      rw [e]; rfl
    rw [hrd, ← prod_baseNorm Dw hx a n]
    change cabs (evR Xo c f y) * _ = _
    rw [hev, cabs_mul, cabs_wchar, mul_right_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hfn i, ← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (cabs_unit_pos _).ne', one_mul]
  · have := isReduced_cAt σ
    have hev := evR_frMap hWD f hf.1 (conjAlg σ) y (hT _ y) y' hm
    change cabs (evR Xo c f y') * _ = cabs (evR Xo c f y) * _
    rw [hev, cabs_conjAlg]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [hP.2 σ y y' hm i]

end GlobalTheory.FrameNorm.Comparison₂
