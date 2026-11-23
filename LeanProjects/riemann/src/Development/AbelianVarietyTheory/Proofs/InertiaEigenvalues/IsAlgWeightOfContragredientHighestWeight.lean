import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgWtDualRead

theorem isAlgWeight_of_hwAtF_dual : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  intro L _ _ _ n K _ e c hc W _ _ _ ρ κ _ _ b ρC hρC τ lam hw
  obtain ⟨ι, _, _, b', P, hP, -⟩ := hw
  classical
  let bd := b.dualBasis
  let A : Matrix κ ι K := bd.toMatrix b'
  let B : Matrix ι κ K := b'.toMatrix bd
  let f : (L →+* K) × Fin n × Fin n → (L →+* K) × Fin n × Fin n := fun p => (p.1.comp c, p.2.2, p.2.1)
  let Q : κ → κ → MvPolynomial ((L →+* K) × Fin n × Fin n) K := fun i j =>
    ∑ l, ∑ k, MvPolynomial.C (A j k) * MvPolynomial.rename f (P k l) * MvPolynomial.C (B l i)
  have key : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : Formalism.AUTREP.GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      ∀ i j, LinearMap.toMatrix b b (ρ γ) i j =
        MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (Q i j) := by
    intro γ γ₀ hm i j
    have hinv := hP γ⁻¹ γ₀⁻¹ (GlobalTheory.WtDual.match_inv γ γ₀ hm)
    have hγ := GlobalTheory.WtDual.mem_rationalUnitaryGroup_of_matrix_match γ γ₀ hm
    have e1 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = Matrix.transpose (LinearMap.toMatrix b b (ρ γ)) := by
      rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    have e2 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = A * LinearMap.toMatrix b' b' (ρ.dual γ⁻¹) * B :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bd b' bd b' _).symm
    have e3 : LinearMap.toMatrix b b (ρ γ) i j = LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) j i := by
      rw [e1]; rfl
    rw [e3, e2]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    simp only [hinv]
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    refine congrArg (fun g => MvPolynomial.eval g (P k l)) (funext fun p => ?_)
    simp only [Function.comp_apply, f, RingHom.comp_apply]
    rw [GlobalTheory.WtDual.inv_entry γ₀ hγ, hc]
    rfl
  refine ⟨inferInstance, κ, inferInstance, inferInstance, Pi.basisFun ℂ κ,
    fun i j => MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n => (e.comp p.1, p.2)) (MvPolynomial.map e (Q i j)), ?_⟩
  intro γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_eq_toMatrix', hρC γ, Matrix.map_apply, key γ γ₀ hm i j, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
  rfl

end GlobalTheory.AlgWtDualRead
