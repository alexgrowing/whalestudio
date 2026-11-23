import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

theorem exists_gaussRing_map :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (σ : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Op X la N) ∧ (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧ (∀ o, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la o) = algebraMap (Op X la N) (Kp X la N) (f o)) ∧ (∀ a : B.KO, φ (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ q, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (σ q)) := by
  intro D B P j X la N D' N' σ
  obtain ⟨f, φ, h1, h2, h3, h4, h5, h6, h7⟩ := gaussRing_completion_rename D B P j X la N D' N' σ
  refine ⟨f, φ, h1, h2, h3, h4, h5, fun a => ?_, h7⟩
  rw [IsScalarTower.algebraMap_apply B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
    (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'), MvPolynomial.algebraMap_eq]
  exact h6 a

end GlobalTheory.GaussCompletion
