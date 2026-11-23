import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormHeightExpSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinear

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice
open scoped Classical

namespace GlobalTheory.ImageModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
  {ev : V →ₗ[K] Ω} {D : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : HermLB p}
  {ψ : Ω →+* X.functionField} {s : W → L.B.Sec}

theorem IsModelOf.fs_sum_pos (hM : IsModelOf Nm W ev D p L ψ s) (hev : ev ≠ 0) {N n : ℕ} {b : Module.Basis (Fin N) K V}
    {g : Matrix (Fin N) (Fin n) K} {A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {c : Matrix (Fin n) (Fin N) K}
    {gw : Fin n → W} (hF : IsFrame Nm W b g A) (hg : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hc : ∀ j, b j = ∑ k, c k j • (gw k : V)) (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K)))
    (hy : y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i)) :
    0 < ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun hS => ?_
  obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
  have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
  have hb := GlobalTheory.frame_semilinear_sq_le K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
    (fun m β u x hx => valR_section_sum K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
  rw [← hS, mul_zero] at hb
  exact hne (by
    have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
    exact norm_eq_zero.1 this)

theorem IsModelOf.fs_shift (hM : IsModelOf Nm W ev D p L ψ s) (hev : ev ≠ 0) (t : ℝ) :
    ∃ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W),
      IsFrame (fun σ x => Real.exp (-t) * Nm σ x) W b g A ∧ (∀ k, (gw k : V) = ∑ j, g j k • b j) ∧
      (∀ j, b j = ∑ k, c k j • (gw k : V)) ∧
      ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))),
        y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) →
        ((L.shift (fun _ => t) (fun _ => rfl)).φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  refine ⟨N, n, b, g, fun σ => ((Real.exp t : ℝ) : ℂ) • A σ, c, gw,
    ⟨hF.span, hF.full, fun σ => ?_, fun σ x => ?_, fun σ x => ?_⟩, hg, hc, fun σ i y hy => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')) (hF.herm σ)
  · simp only [GlobalTheory.HeightShift.frameNorm_exp_smul (hF.herm _)]
    rw [hF.conj σ x]
  · rw [GlobalTheory.HeightShift.frameNorm_exp_smul (hF.herm _), hF.norm]
  · have hpos := hM.fs_sum_pos hev hF hg hc σ i y hy
    have e : ∑ a, ‖∑ k, (∑ m, σ (c k m) * (((Real.exp t : ℝ) : ℂ) • A σ) m a) *
          valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 =
        Real.exp t ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ∑ k, (∑ m, σ (c k m) * (((Real.exp t : ℝ) : ℂ) • A σ) m a) * valR y.1 (L.B.U i) ((s (gw k)).f i) =
          ((Real.exp t : ℝ) : ℂ) * ∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]; ring
      rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [e, Real.log_mul (pow_pos (Real.exp_pos _) 2).ne' hpos.ne', Real.log_pow, Real.log_exp, ← hφ σ i y]
    change (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y + 2 * t = _
    push_cast
    ring

end GlobalTheory.ImageModel
