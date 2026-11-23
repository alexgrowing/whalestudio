import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLeStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusBound

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ Q : Set (GA D V), IsCompact Q → ∀ Φ : schwartzA θ V.rank n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ y ∈ Q, GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc Q hQ Φ
  have hSB := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ V.rank n Φ.1 hSB
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ V n Q hQ K hK
  obtain ⟨N, C₁, hC₁, hframe⟩ := GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le D θ hθ V n r X Y hXY c hc K' hK'
  obtain ⟨C₀, hC₀⟩ := hmaj N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  set A : ℝ := max C₀ 0 * C₂ with hA
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) hC₂
  refine ⟨A * C₁, mul_nonneg hA0 hC₁, ?_⟩
  intro t ht a ha y hy
  have hpt : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      GlobalTheory.SiegelFormula.invPt V (a * y) ξ
        = (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (GlobalTheory.SiegelFormula.invPt V a ξ) : Mx D V.rank n) := by
    intro ξ
    have h2 : Formalism.L2.Theta.mt V (a * y)⁻¹ = Formalism.L2.Theta.mt V y⁻¹ * Formalism.L2.Theta.mt V a⁻¹ := by
      rw [mul_inv_rev]; rfl
    simp only [GlobalTheory.SiegelFormula.invPt, h2, Matrix.mul_assoc]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ
        ≤ ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := by
    intro ξ
    rw [← ENNReal.ofReal_mul hA0, ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [hpt ξ]
    set x := GlobalTheory.SiegelFormula.invPt V a ξ
    have h1 := hC₀ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    have h2 := hmul' y hy x
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    calc ‖Φ.1 (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)‖
        ≤ C₀ * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := h1
      _ ≤ max C₀ 0 * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ max C₀ 0 * (C₂ * GlobalTheory.Unf.maj θ K' N x) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = A * GlobalTheory.Unf.maj θ K' N x := by rw [hA, mul_assoc]
  calc GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ := rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal A * ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        by gcongr; exact hframe t ht a ha
    _ = ENNReal.ofReal (A * C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_mul hA0]; congr 1; ring

end GlobalTheory.TorusBound
