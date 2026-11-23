import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem smallSec_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ t hw ht j hj τ y
  obtain ⟨N, n', b, g, A, c, gw, hF, hgw, hb, hφ⟩ := hM.fs
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ :=
    ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp τ⟩
  refine (le_of_eq (GlobalTheory.HermLB.nsq_shift L (fun _ => t) (fun _ => rfl)
    (GlobalTheory.CxPts.secVal p _ (s ⟨w j, hj⟩)) y)).trans ?_
  set i := GlobalTheory.CxPts.pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y with hi_def
  have hi := GlobalTheory.CxPts.mem_pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y
  rw [GlobalTheory.Weight.nsq_eq _ (GlobalTheory.CxPts.secVal_mem _) hi, GlobalTheory.CxPts.secVal_apply, hφ σ i y]
  set ℓ : W → ℂ := fun x => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) with hℓ
  have hlin : ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) →
      ℓ x = ∑ k, σ (β k : K) * ℓ (u k) := fun m β u x hx =>
    GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hi m β u x hx
  have hbd := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n' b g A c gw σ ℓ hF hgw hb hlin ⟨w j, hj⟩
  set S := ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hev' : GlobalTheory.CxPts.ev p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) ((s ⟨w j, hj⟩).f i) y = ℓ ⟨w j, hj⟩ := rfl
  rw [hev']
  have hNm0 : 0 ≤ Nm σ (w j) := by
    rw [← hF.norm σ (w j)]; exact Real.sqrt_nonneg _
  have hNm : Nm σ (w j) ≤ abelian₂ := hw.le j σ
  have hLam0 : 0 < abelian₂ := lt_of_lt_of_le one_pos hw.one_le
  have hLt : abelian₂ ≤ Real.exp t := (Real.log_le_iff_le_exp hLam0).1 ht
  have hLam2 : abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ 1 := by
    have h1 : abelian₂ ^ 2 ≤ Real.exp t ^ 2 := pow_le_pow_left₀ hLam0.le hLt 2
    have h2 : Real.exp t ^ 2 * Real.exp (-(2 * t)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    calc abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ Real.exp t ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := h2
  rcases hS0.eq_or_lt with h0 | hpos
  · have : ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ 0 := by simpa [← h0] using hbd
    have hz : ‖ℓ ⟨w j, hj⟩‖ ^ 2 = 0 := le_antisymm this (sq_nonneg _)
    rw [hz]; simp
  · rw [Real.exp_neg, Real.exp_log hpos]
    have h3 : ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ ≤ abelian₂ ^ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ Nm σ (w j) ^ 2 * S := hbd
        _ ≤ abelian₂ ^ 2 * S := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNm0 hNm 2) hS0
    calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ * Real.exp (-(2 * t)) ≤ abelian₂ ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ 1 := hLam2

end GlobalTheory.ImageModel
