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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgSubrep

theorem toMatrix_sandwich {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (e : Module.Basis κ ℂ U) (π : V →ₗ[ℂ] U) (s : U →ₗ[ℂ] V)
    (f : V →ₗ[ℂ] V) :
    LinearMap.toMatrix e e (π ∘ₗ f ∘ₗ s) =
      LinearMap.toMatrix b e π * LinearMap.toMatrix b b f * LinearMap.toMatrix e b s := by
  rw [LinearMap.toMatrix_comp e b e, LinearMap.toMatrix_comp e b b, Matrix.mul_assoc]

theorem eval_sandwich {ι κ σ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (B : Matrix ι κ ℂ)
    (P : ι → ι → MvPolynomial σ ℂ) (x : σ → ℂ) (M : Matrix ι ι ℂ)
    (hM : M = fun k l => MvPolynomial.eval x (P k l)) :
    A * M * B =
      fun i j => MvPolynomial.eval x (∑ k, ∑ l, MvPolynomial.C (A i k) * P k l * MvPolynomial.C (B l j)) := by
  funext i j
  simp only [Matrix.mul_apply, Finset.sum_mul]
  subst hM
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [Finset.sum_comm]

end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem isAlgWeight_subrep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V)
    (hρ : Formalism.AUTREP.IsAlgWeight L n ρ) (S : Subrepresentation ρ) :
    Formalism.AUTREP.IsAlgWeight L n S.toRepresentation := by
  classical
  obtain ⟨hfin, ι, _, _, b, P, hP⟩ := hρ
  haveI := hfin
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S.toSubmodule
  let π : V →ₗ[ℂ] S.toSubmodule := Submodule.linearProjOfIsCompl S.toSubmodule C hC
  let e := Module.Free.chooseBasis ℂ S.toSubmodule
  refine ⟨inferInstance, Module.Free.ChooseBasisIndex ℂ S.toSubmodule, inferInstance, inferInstance, e,
    fun i j => ∑ k, ∑ l, MvPolynomial.C (LinearMap.toMatrix b e π i k) * P k l *
      MvPolynomial.C (LinearMap.toMatrix e b S.toSubmodule.subtype l j), ?_⟩
  intro γ γ₀ hγ
  have hres : S.toRepresentation γ = π ∘ₗ ρ γ ∘ₗ S.toSubmodule.subtype := by
    ext x : 1
    have hm : ρ γ x ∈ S.toSubmodule := S.apply_mem_toSubmodule γ x.2
    have h1 := Submodule.linearProjOfIsCompl_apply_left hC ⟨ρ γ x, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [show π (ρ γ ↑x) = _ from h1]
    apply Subtype.ext
    rfl
  have h4 := hP γ γ₀ hγ
  have h5 := toMatrix_sandwich b e π S.toSubmodule.subtype (ρ γ)
  exact (congrArg (LinearMap.toMatrix e e) hres).trans
    (h5.trans (eval_sandwich (LinearMap.toMatrix b e π) (LinearMap.toMatrix e b S.toSubmodule.subtype) P _ _ h4))
end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem exists_irreducible_algWt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V), Formalism.AUTREP.IsAlgWeight L n ρ → ∃ (a : NG.AlgWt L n) (j : a.W →ₗ[ℂ] V), Function.Injective j ∧ ∀ γ x, j (a.ρ γ x) = ρ γ (j x) := by
  intro L _ _ _ n V _ _ _ ρ hρ
  haveI := hρ.1
  obtain ⟨S, hS⟩ := GlobalTheory.PiIsotypic.exists_irreducible_subrep ρ
  exact ⟨⟨S.toSubmodule, S.toRepresentation, isAlgWeight_subrep L n ρ hρ S, hS⟩,
    S.toSubmodule.subtype, S.toSubmodule.injective_subtype, fun γ x => rfl⟩

end GlobalTheory.AlgSubrep
