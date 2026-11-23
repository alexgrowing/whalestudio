import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencerStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DerivationEqZeroOfKodairaSpencerZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerCommutesWithEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerMatrixLinearInDerivationStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassIsSymmOfLiftStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS

theorem tangent_injects_symm_antilinear : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))), (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∃ (t₀ : TObj g k J b (spMap (algebraMap o ℂ))) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ) (κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ), GoodU u Hm χ ∧ (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) ∧ Function.Injective κ ∧ ∀ D, IsSymm Hm (κ D) ∧ ∀ (f : t.A ⟶ t.A) (f₀ : t₀.pol.A ⟶ t₀.pol.A) (F : (Fin t₀.pol.g → ℂ) →ₗ[ℂ] (Fin t₀.pol.g → ℂ)), f₀.left ≫ m = m ≫ f.left → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm (κ D) F := by
  intro h1 h2 hU o _ g k J b R _ _ _ _ _ t hun
  have hcomp : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [IsScalarTower.algebraMap_eq o R ℂ]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap o R)) (CommRingCat.ofHom (algebraMap R ℂ))).symm
  obtain ⟨t₀, m, hm⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ (spMap (algebraMap R ℂ)) t hcomp
  obtain ⟨u, Hm, χ, hG, -⟩ := GlobalTheory.T.exists_goodUniformisation_kodairaSpencer hU t₀.pol
  have hsm : Smooth t.A.hom := by
    haveI := t.dim
    exact SmoothOfRelativeDimension.smooth g _
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation t₀.pol u Hm χ hG o R t.A.left t.A.hom m hsm hm.1.1
  refine ⟨t₀, m, u, Hm, χ, κ, hG, hm, ?_, fun D => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨s, hs⟩ := hκ D
    rw [hD] at hs
    exact GlobalTheory.T.derivation_eq_zero_of_kodairaSpencer_zero h1 h2 hU o g k J b R t _ t₀ m u Hm χ hG hm hun D s hs
  · obtain ⟨s, hs⟩ := hκ D
    refine ⟨GlobalTheory.T.kodairaSpencer_class_isSymm_of_lift t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs t.L t.isLB hm.2.1, ?_⟩
    intro f f₀ F hf hF
    exact GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs f.left f₀ F (Over.w f) hf hF

end GlobalTheory.KS
