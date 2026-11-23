import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothSpanLeMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MspanLeBddForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApplyScalar

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.ThetaPoisson GroundTheory.Global GlobalTheory.RSThetaLow
open GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.RSResidue

theorem continuous_integral_of_compact {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] {K : Set Y} (hK : IsCompact K)
    {F : X → Y → ℂ} (hF : Continuous fun p : X × Y => F p.1 p.2) (h0 : ∀ x, ∀ y ∉ K, F x y = 0) :
    Continuous fun x => ∫ y, F x y ∂ν := by
  have hI : (fun x => ∫ y, F x y ∂ν) = fun x => ∫ y in K, F x y ∂ν :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
  rw [hI]
  have hc : ∀ x, Continuous (F x) := fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (F x) K ν := fun x => (hc x).continuousOn.integrableOn_compact hK
  set m : ℝ := ν.real K with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hδ : 0 < ε / (m + 1) := by positivity
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, dist (F x y) (F x₀ y) < ε / (m + 1) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := Metric.tendsto_nhds.1 (hF.continuousAt (x := (x₀, y))) (ε / (m + 1) / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.1 ((hc x₀).comp continuous_snd |>.continuousAt (x := (x₀, y)))
      (ε / (m + 1) / 2) (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F z.1 z.2) (F x₀ z.2) ≤ dist (F z.1 z.2) (F x₀ y) + dist (F x₀ z.2) (F x₀ y) :=
          dist_triangle_right _ _ _
      _ < ε / (m + 1) / 2 + ε / (m + 1) / 2 := add_lt_add hz1 hz2
      _ = ε / (m + 1) := by ring
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have h3 : ‖∫ y in K, (F x y - F x₀ y) ∂ν‖ ≤ ε / (m + 1) * m :=
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y hy => by
      rw [← dist_eq_norm]; exact (hx y hy).le
  refine h3.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero_eq {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) : ∃ c : ℂ, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 = (∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a) * c := by
  refine ⟨(finiteAdelicChar E (∑ i, η i * pFin E ((0 : Fin a → Ad E) i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E ((0 : Fin a → Ad E) i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ), fun g => ?_⟩
  have h := rsHat_eq (ℓ := ℓ) J η F F' hΦ g 0
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have hF : infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E ((0 : Fin a → Ad E) i)) =
      ∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a := by
    rw [e, infFourier]
    simp
  change rsHat ℓ F.1 F'.1 Φ J η g 0 = _
  rw [h, hF]
  ring

variable {ω : HChar E}

theorem rsHat_zero_props (hω : ω.IsUnitary) {φ φ' : Sm E a} (h : φ.1 ∈ bddForms E a ω) (h' : φ'.1 ∈ bddForms E a ω)
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) :
    Continuous (fun g : GA E a => adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0) ∧
    (∃ C : ℝ, ∀ g : GA E a, ‖adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0‖ ≤ C) ∧
    ∀ γ ∈ latticeGL E a, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g)) 0 = adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 := by
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hc]
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc, norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ hγ g
    have hL : ∀ x, φ.1 (γ * x) * conj (φ'.1 (γ * x)) = φ.1 x * conj (φ'.1 x) := fun x =>
      leftInv_mul_conj hω h h' γ hγ x
    have e : rsInf ℓ φ.1 φ'.1 Φ (γ * g) = rsInf ℓ φ.1 φ'.1 Φ g := funext fun u => by
      rw [rsInf, rsInf, mul_assoc γ g, hL]
    have e' : rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y => by
      rw [rsPsi, rsPsi, e]
    rw [e']

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

end GlobalTheory.RSResidue

end
