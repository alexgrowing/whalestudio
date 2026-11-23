import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.St

theorem col_mul_eq_mulVec {A : Type} [CommRing A] {n ι κ : Type} [Fintype n] [Fintype ι]
    (M : Matrix n ι A) (B : Matrix ι κ A) (c : κ) :
    M *ᵥ (fun i => B i c) = fun i => (M * B) i c := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem rational_unitary_extend_by_identity : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, hG', hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hU := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _ X.B.I.J
    ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) G' Q Qi hQQi hQiQ hblk hG').1 y₀ hy
  set M := Q * Matrix.fromBlocks y₀ 0 0 (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) * Qi with hM
  have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
  have hdet : IsUnit M.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := X.B.I.J⁻¹ * ((M.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J)) ?_
    rw [Matrix.mul_assoc, hU, Matrix.nonsing_inv_mul _ hJu]
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  have hMQ : M * Q = Q * Matrix.fromBlocks y₀ 0 0 1 := by
    rw [hM, Matrix.mul_assoc, hQiQ, Matrix.mul_one]
    rfl
  refine ⟨hMu.unit, ?_, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd X.B.I.E) (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J * (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J
    rw [IsUnit.unit_spec]
    exact hU
  · intro x hx
    rw [IsUnit.unit_spec]
    have key : ∀ b, M *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b) := by
      intro b
      rw [col_mul_eq_mulVec, hMQ]
      funext i
      erw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
    · have := key (Sum.inl a)
      have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext fun i => he a i
      rwa [e] at this
    · have := key (Sum.inr (Sum.inl a))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext fun i => hf a i
      rwa [e] at this
    · rw [Set.mem_singleton_iff] at hz'
      subst hz'
      have := key (Sum.inr (Sum.inr ()))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
      rwa [e] at this
  · intro j
    rw [IsUnit.unit_spec]
    have e : ∀ j, X.crd (qFr wt j) = fun i => Q i (Sum.inl j) := fun j => funext fun i => (hq j i).symm
    rw [e j, col_mul_eq_mulVec, hMQ]
    funext r
    simp only [e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    erw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.St
