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

namespace GlobalTheory.ImageModelSemi

open GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem semiPos_of_isModelOf : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  intro τ
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := ⟨_, extEmb_comp τ⟩
  let M : Matrix (Fin n) (Fin N) ℂ := fun k a => ∑ m, σ (c k m) * A σ m a
  have hz : Weight.NoCommonZero fun a =>
      ∑ j, M j a • secVal p (σ.comp (algebraMap (𝓞 K) K)) (s (gw j)) := by
    intro i y hy
    by_contra! h0
    have hS : ∑ a, ‖∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have h1 := h0 a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [show (∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)) = 0 from h1]
      simp
    obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
    have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
    have hb := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
      (fun m β u x hx => GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
    rw [hS, mul_zero] at hb
    exact hne (by
      have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
      exact norm_eq_zero.1 this)
  have key : (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ = (combWeight L.isLB (fun k => s (gw k)) M hz).φ :=
    funext fun i => funext fun y => (hφ σ i y).trans (combWeight_φ L.isLB (fun k => s (gw k)) M hz i y).symm
  intro i ch y hy ξ
  have := semiPosReg_combWeight L.isLB (fun k => s (gw k)) M hz D i ch y hy ξ
  rw [key]
  exact this

end GlobalTheory.ImageModelSemi
