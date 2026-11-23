import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusConStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementPropertiesStatement
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem lintegral_comp_scale {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, 0 < s a)
    (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p : (Fin r → ℂ) × ℂ, G (fun a => (s a : ℂ) * p.1 a, p.2) =
      ENNReal.ofReal (∏ a, (s a ^ 2)⁻¹) * ∫⁻ p, G p := by
  let f : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    LinearMap.pi fun i => ((s i • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)
  let T : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) := f.prodMap LinearMap.id
  have hdet : LinearMap.det T = ∏ a, s a ^ 2 := by
    simp only [T, f, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id,
      Complex.finrank_real_complex, mul_one]
  have hpos : 0 < ∏ a, s a ^ 2 := Finset.prod_pos fun a _ => pow_pos (hs a) 2
  have hne : LinearMap.det T ≠ 0 := hdet ▸ hpos.ne'
  haveI : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ((Fin r → ℂ) × ℂ)) hne
  let e : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) :=
    (T.equivOfDetNeZero hne).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : _ → _) = T := rfl
  have h := lintegral_map_equiv (μ := (volume : Measure ((Fin r → ℂ) × ℂ))) G e
  rw [he, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos), smul_eq_mul] at h
  rw [Finset.prod_inv_distrib, h]
  refine lintegral_congr fun p => ?_
  congr 1

theorem bcWeight_scale (k r : ℕ) (T T' : ℝ) (s : Fin r → ℝ) (hs : ∀ a, 0 < s a) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r T T' p = (∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹) *
      bcWeight k r T T' (fun a => (s a : ℂ) * p.1 a, p.2) := by
  unfold bcWeight
  split_ifs with h
  · rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    have := (hs a).ne'
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs a), mul_pow]
    field_simp
  · simp

theorem gamLev_inv_eq (k r : ℕ) (t : ℝ) (ht : 0 < t) :
    (D.GamLev k r t⁻¹ 1 0)⁻¹ = (∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ (2 * (Mdim k r a - 2)))⁻¹) *
      ∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ 2)⁻¹ := by
  unfold D.GamLev
  rw [Finset.prod_Ioc_succ_top (Nat.zero_le r), ← Finset.prod_mul_distrib]
  have h1 : Finset.Ioc 0 r = Finset.Ico 1 (r + 1) := by ext; simp; omega
  rw [h1, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
  have h0 : ((r : ℤ) + 1 - ((r + 1 : ℕ) : ℤ)) = 0 := by push_cast; ring
  rw [h0]
  simp only [mul_zero, zero_mul, neg_zero, zpow_zero, div_one, mul_one]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  obtain ⟨d, hd⟩ : ∃ d, r = a.val + (d + 1) := ⟨r - a.val - 1, by have := a.isLt; omega⟩
  have h2 : r - a.val = d + 1 := by omega
  have h3 : Mdim k r a - 2 = 2 * d + k + 1 := by unfold Mdim; omega
  have h4 : 4 * ((r : ℤ) + 1 - ((1 + a.val : ℕ) : ℤ)) * (C.Mlev k r (1 + a.val) - 1) =
      ((2 * (d + 1) * (2 * (2 * d + k + 1)) + 2 * (d + 1) * 2 : ℕ) : ℤ) := by
    unfold C.Mlev
    have : (r : ℤ) = a.val + (d + 1) := by exact_mod_cast hd
    push_cast
    rw [this]; ring
  rw [h4, h2, h3, _root_.inv_zpow', neg_neg, zpow_natCast, ← pow_mul, ← pow_mul, pow_add, mul_inv]

theorem energy_change_of_frame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  intro k r L μsec Bs cN F _ hstd hrat hc h0 htop
  have hJ := GlobalTheory.T.besselFunction_eq_scalar_sq_normalisedBessel_torusConjugate k r L μsec Bs cN F hstd hrat hc h0 htop
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  set α := cStd / L.c with hαdef
  have hB := (GlobalTheory.T.besselTorusElement_properties k r α hα).2.2.2
  have ht : 0 < ‖α‖ := norm_pos_iff.2 hα
  obtain ⟨hz, hz', -, -, -, -, -, hμ⟩ := hstd
  let s : Fin r → ℝ := fun a => ‖α‖ ^ (2 * (r - a.val))
  have hs : ∀ a, 0 < s a := fun a => pow_pos ht _
  let G : (Fin r → ℂ) × ℂ → ENNReal := fun p =>
    ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      ‖B.hsVec (B.JF Bs (conjF α F) (B.gq Bs p))‖ ^ 2)
  have hG : B.normSq Bs (conjF α F) = ∫⁻ p, G p := by
    simp only [B.normSq, jNormSq, hz, hz', G]
  let A : ℝ := lamN L cN ^ 4 * ∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_pos (hs a) _).le)
  have hhs : ∀ X : L.Wq →L[ℂ] L.Wp, Formalism.MainNotions.S.hsNormSq X = ‖B.hsVec X‖ ^ 2 := by
    intro X
    rw [PiLp.norm_sq_eq_of_L2]
    unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpt : ∀ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) =
      ENNReal.ofReal A * G (fun a => (s a : ℂ) * p.1 a, p.2) := by
    intro p
    simp only [G]
    rw [← ENNReal.ofReal_mul hA, hJ, hB, hhs, bcWeight_scale k r _ _ s hs p]
    congr 1
    have hsm : ∀ (c : ℂ) (X : L.Wq →L[ℂ] L.Wp), B.hsVec (c • X) = c • B.hsVec X := fun _ _ => rfl
    rw [hsm, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [B.gq, hμ, A, s]
    ring
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_scale s hs G,
    hG, ← mul_assoc, ← ENNReal.ofReal_mul hA, div_eq_mul_inv, gamLev_inv_eq k r _ ht]
  simp only [A, s, mul_assoc]

end GlobalTheory.ThA
