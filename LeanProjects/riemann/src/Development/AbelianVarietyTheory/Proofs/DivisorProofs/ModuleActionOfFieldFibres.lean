import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFreeOfMaximalIdealGeneratorStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem residueField_exists_algebraMap_mul_eq (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime]
    (k : p.ResidueField) : ∃ a s : R, algebraMap R p.ResidueField s ≠ 0 ∧
      algebraMap R p.ResidueField s * k = algebraMap R p.ResidueField a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective k
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  refine ⟨a, s, ?_, ?_⟩
  · rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  · rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField a]
    simp only [IsLocalRing.ResidueField.algebraMap_eq]
    rw [← map_mul, IsLocalization.mk'_spec']

theorem invertible_of_fibres_invertible : ∀ (R O : Type) [CommRing R] [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] (M : Type)
    [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M] [Module.Finite R M] [Module.Projective R M],
    (∀ (K : Type) [Field K] [Algebra R K], ∃ (N : Type) (_ : AddCommGroup N) (_ : Module K N) (_ : Module O N)
      (_ : SMulCommClass K O N) (e : K ⊗[R] M ≃ₗ[K] N),
      (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) ∧
      letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
      Module.Invertible (K ⊗[ℤ] O) N) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  intro R O _ _ _ _ M _ _ _ _ _ _ hK
  let b := Module.Free.chooseBasis ℤ O
  refine GlobalTheory.T.locally_free_of_maximal_ideal_generator R O _ b M fun p hp => ?_
  obtain ⟨N, _, _, _, _, e, he, hinv⟩ := hK p.ResidueField
  obtain ⟨m, hm⟩ := GlobalTheory.T.module_action_fraction_field R O _ b M p.ResidueField
    (residueField_exists_algebraMap_mul_eq R p) N e he hinv
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.T.exists_local_generators_residue_basis R M _ (fun i => b i • m) p hm
  exact ⟨g, hg, m, h1, h2⟩

end GlobalTheory
