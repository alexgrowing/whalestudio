import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem det_eq_one_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  simp [fun i => (h i i).2]

theorem mem_UX_iff_entries {D : D7} {ρ : ℕ} (v : GL (Fin ρ) (AE D)) :
    v ∈ UX D ρ ↔ ∀ i j : Fin ρ, (j < i → v.val i j = 0) ∧ v.val i i = 1 := Iff.rfl

theorem exists_unit_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) :
    ∃ v : GL (Fin ρ) A, v.val = M ∧ (v⁻¹).val = M.adjugate := by
  have hdet := det_eq_one_of_upperUni h
  refine ⟨⟨M, M.adjugate, ?_, ?_⟩, rfl, rfl⟩
  · rw [Matrix.mul_adjugate, hdet, one_smul]
  · rw [Matrix.adjugate_mul, hdet, one_smul]

theorem isCompact_setOf_rat_mul_mem : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  intro D n ρ x₀ hx K hK
  obtain ⟨-, hT2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hinj : Function.Injective x₀.mulVec := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin x₀) (LinearMap.ker_eq_bot.2 hinj)
  have hL : LinearMap.toMatrix' g * x₀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLr : rat (LinearMap.toMatrix' g) ⬝ rat x₀ = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := by
    simp only [rat]
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set S' : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    {M | (∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) ∧ rat x₀ ⬝ M ∈ K} with hS'def
  have hC : IsCompact ((fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K) :=
    hK.image (continuous_const.matrix_mul continuous_id)
  have hsub : S' ⊆ (fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K := by
    rintro M ⟨-, hM⟩
    exact ⟨_, hM, by simp only [← Matrix.mul_assoc, hLr, Matrix.one_mul]⟩
  have hcl : IsClosed S' := by
    rw [hS'def, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (hK.isClosed.preimage ((continuous_const (y := (rat x₀ : Mx D n ρ))).matrix_mul (continuous_id (X := Matrix (Fin ρ) (Fin ρ) (AE D)))))
    rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    rw [Set.setOf_and]
    exact (isClosed_imp isOpen_const (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hS' : IsCompact S' := hC.of_isClosed_subset hcl hsub
  let ι : UX D ρ → Matrix (Fin ρ) (Fin ρ) (AE D) × (Matrix (Fin ρ) (Fin ρ) (AE D))ᵐᵒᵖ := fun u => Units.embedProduct _ u.1
  have hι : Topology.IsEmbedding ι := Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  have hF : Continuous (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate)
  have heq : ι '' {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} = (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) '' S' := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hU : ∀ i j : Fin ρ, (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
      refine ⟨u.1.1, ⟨hU, hu⟩, ?_⟩
      have hdet := det_eq_one_of_upperUni hU
      refine Prod.ext rfl ?_
      show MulOpposite.op u.1.1.adjugate = MulOpposite.op (Units.val (u.1)⁻¹)
      congr 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    · rintro ⟨M, ⟨hU, hM⟩, rfl⟩
      have hdet := det_eq_one_of_upperUni hU
      obtain ⟨v, hv1, hv2⟩ := exists_unit_of_upperUni hU
      subst hv1
      have hmem : v ∈ UX D ρ := (mem_UX_iff_entries v).2 hU
      refine ⟨⟨v, hmem⟩, hM, ?_⟩
      exact Prod.ext rfl (congrArg MulOpposite.op hv2)
  rw [hι.isInducing.isCompact_iff, heq]
  exact hS'.image hF

end GlobalTheory.AscFin

end
