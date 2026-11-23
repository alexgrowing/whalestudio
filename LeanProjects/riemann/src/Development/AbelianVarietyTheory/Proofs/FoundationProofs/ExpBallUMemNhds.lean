import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory.ExpBallNhds

theorem exp_local_algebra (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (∃ S ∈ 𝓝 (0 : A), Set.InjOn (NormedSpace.exp : A → A) S) ∧
      Filter.map (NormedSpace.exp : A → A) (𝓝 0) = 𝓝 1 := by
  have h : HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)
  refine ⟨⟨(h.toOpenPartialHomeomorph _).source, ?_, ?_⟩, ?_⟩
  · exact (h.toOpenPartialHomeomorph _).open_source.mem_nhds h.mem_toOpenPartialHomeomorph_source
  · have := (h.toOpenPartialHomeomorph _).injOn
    simpa using this
  · have := h.map_nhds_eq_of_equiv
    rwa [NormedSpace.exp_zero] at this

theorem exp_local_matrix (n : Type) [Fintype n] [DecidableEq n] :
    (∃ S ∈ 𝓝 (0 : Matrix n n ℂ), Set.InjOn (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) S) ∧
      Filter.map (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (𝓝 0) = 𝓝 1 := by
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  exact exp_local_algebra (Matrix n n ℂ)

theorem Jpq_mul_self (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

open MeasureTheory Filter Topology in
private theorem exists_local_homeomorph_matrix_exp_source_zero {n : Type} [Fintype n] [DecidableEq n] :
    ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
      (0 : Matrix n n ℂ) ∈ e.source ∧ ⇑e = NormedSpace.exp := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)) 0 :=
    hasStrictFDerivAt_exp_zero
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source,
    hf.toOpenPartialHomeomorph_coe⟩

open MeasureTheory Filter Topology in
open Matrix in

theorem _root_.GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds : ∀ (P Q : ℕ) (r : ℝ), 0 < r →
    {g : _root_.Formalism.BasicNotions.UpqT P Q | ∃ X ∈ _root_.Formalism.BasicNotions.ballU P Q r,
      _root_.Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} ∈
      𝓝 (1 : _root_.Formalism.BasicNotions.UpqT P Q) := by
  intro P Q r hr
  obtain ⟨e, h0, he⟩ := exists_local_homeomorph_matrix_exp_source_zero (n := Fin P ⊕ Fin Q)
  set J := _root_.Formalism.UG.Jpq P Q with hJ
  have hJJ : J * J = 1 := by
    rw [hJ]; unfold _root_.Formalism.UG.Jpq; simp [fromBlocks_multiply]
  have hJinv : J⁻¹ = J := Matrix.inv_eq_right_inv hJJ
  have hJunit : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  set σ : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    fun X => -(J * Xᴴ * J) with hσ
  have hσc : Continuous σ := by
    rw [hσ]
    exact ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
      continuous_const).neg
  have hσ0 : σ 0 = 0 := by simp [hσ]
  set N : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := {X | ∑ i, ∑ j, ‖X i j‖ < r} with hN
  have hNo : IsOpen N := isOpen_lt (by fun_prop) continuous_const
  have hU : e.source ∩ σ ⁻¹' e.source ∩ N ∈ 𝓝 (0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    refine ((e.open_source.inter (e.open_source.preimage hσc)).inter hNo).mem_nhds ⟨⟨h0, ?_⟩, ?_⟩
    · show σ 0 ∈ e.source
      rw [hσ0]; exact h0
    · show ∑ i, ∑ j, ‖(0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r
      simpa using hr
  have himg := e.image_mem_nhds h0 hU
  rw [he, NormedSpace.exp_zero] at himg
  have hmat : Continuous (fun g : _root_.Formalism.BasicNotions.UpqT P Q => _root_.Formalism.BasicNotions.UpqT.mat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hpre : (fun g : _root_.Formalism.BasicNotions.UpqT P Q => _root_.Formalism.BasicNotions.UpqT.mat g) ⁻¹'
      (NormedSpace.exp '' (e.source ∩ σ ⁻¹' e.source ∩ N)) ∈ 𝓝 (1 : _root_.Formalism.BasicNotions.UpqT P Q) :=
    hmat.continuousAt.preimage_mem_nhds himg
  filter_upwards [hpre] with g hg
  obtain ⟨X, ⟨⟨hXs, hσXs⟩, hXN⟩, hgX⟩ := hg
  beta_reduce at hgX
  have hgU : (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = J := g.2
  have hexpσ : NormedSpace.exp (σ X) = NormedSpace.exp X := by
    have hleft : J * (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = 1 := by
      rw [show J * (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = J * ((_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g)
        by simp only [mul_assoc], hgU, hJJ]
    rw [hσ]
    show NormedSpace.exp (-(J * Xᴴ * J)) = _
    have hc := Matrix.exp_conj J Xᴴ hJunit
    rw [hJinv] at hc
    rw [Matrix.exp_neg, hc, Matrix.exp_conjTranspose, hgX, Matrix.inv_eq_right_inv hleft]
  have hσX : σ X = X := e.injOn hσXs hXs (by rw [he]; exact hexpσ)
  have hJX : J * X = -(Xᴴ * J) := by
    conv_lhs => rw [← hσX]
    rw [hσ]
    show J * -(J * Xᴴ * J) = _
    rw [mul_neg, ← mul_assoc, ← mul_assoc, hJJ, one_mul]
  have hlie : X ∈ _root_.Formalism.BasicNotions.lieU P Q := by
    show Xᴴ * _root_.Formalism.UG.Jpq P Q + _root_.Formalism.UG.Jpq P Q * X = 0
    rw [← hJ, hJX, add_neg_cancel]
  exact ⟨⟨X, hlie⟩, hXN, hgX.symm⟩

end GlobalTheory.ExpBallNhds
