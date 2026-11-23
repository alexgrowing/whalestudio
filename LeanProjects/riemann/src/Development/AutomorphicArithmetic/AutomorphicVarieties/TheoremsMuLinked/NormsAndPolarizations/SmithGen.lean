import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.G6Decomposition
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.smith_gen {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (P : GL (Fin n) K) : ∃ (U V : GL (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖(U : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((U⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖(V : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((V⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) K) = U * diagonal d * V :=
  _root_.UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen P

theorem UpperTheory.V.Th.Nm.smith :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (P : GL (Fin n) (Qbar l)), ∃ (U V : GL (Fin n) (Qbar l)) (d : Fin n → Qbar l), IntM (U : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((U⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM (V : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) (Qbar l)) = U * diagonal d * V := by
  intro l _ n P
  exact smith_gen P
