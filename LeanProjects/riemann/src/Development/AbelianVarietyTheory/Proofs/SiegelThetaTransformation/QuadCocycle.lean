import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpaceStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HermComp

variable {N : ℕ}

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {N : ℕ} in

theorem _root_.GlobalTheory.SW.HermComp.row_rel (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (h : gᴴ * Matrix.J (Fin N) ℂ * g = Matrix.J (Fin N) ℂ) :
    g.toBlocks₁₁ * g.toBlocks₂₂ᴴ - g.toBlocks₁₂ * g.toBlocks₂₁ᴴ = 1 ∧
      g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = g.toBlocks₂₁ * g.toBlocks₂₂ᴴ := by
  set J := Matrix.J (Fin N) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hleft : (-(J * gᴴ * J)) * g = 1 := by
    have : J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, this, h, hJJ, neg_neg]
  have hright : g * (-(J * gᴴ * J)) = 1 := mul_eq_one_comm.mp hleft
  have hgJ : g * J * gᴴ = J := by
    have h1 : g * J * gᴴ * J = -1 := by
      have := congrArg Neg.neg hright
      simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
    calc g * J * gᴴ = g * J * gᴴ * J * (-J) := by
            rw [Matrix.mul_assoc (g * J * gᴴ), Matrix.mul_neg, hJJ, neg_neg, Matrix.mul_one]
      _ = J := by rw [h1, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  rw [← Matrix.fromBlocks_toBlocks g] at hgJ
  simp only [J, Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hgJ
  obtain ⟨-, h12, -, h22⟩ := hgJ
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul] at h12 h22
  constructor
  · rw [← neg_inj, neg_sub, ← h12]; abel
  · rw [← sub_eq_zero, ← h22]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_unitary (τ : E →+* ℂ) (γ : M2 E N) (h : γ ∈ UU E N) :
    (γ.map τ)ᴴ * Matrix.J (Fin N) ℂ * γ.map τ = Matrix.J (Fin N) ℂ := by
  have hJ : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
    simpa using Matrix.map_J (Fin N) τ
  have hc : (ccT γ).map τ = (γ.map τ)ᴴ := by
    ext a b
    simp only [ccT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, cc]
    exact IsCMField.complexEmbedding_complexConj E τ _
  have := congrArg (fun M : M2 E N => M.map τ) h
  simpa only [Matrix.map_mul, hJ, hc] using this

end GlobalTheory.SW.HermComp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem inv_denominator_mul_lower_left_cocycle {N : ℕ}
    {A B C D C' D' Z : Matrix (Fin N) (Fin N) ℂ}
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hdet0 : (C * Z + D).det ≠ 0)
    (hdet1 : (C' * ((A * Z + B) * (C * Z + D)⁻¹) + D').det ≠ 0) :
    ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D') * (C * Z + D))⁻¹ * (C' * A + D' * C) =
      (C * Z + D)⁻¹ * ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D')⁻¹ * C') * (Z * Cᴴ + Dᴴ)⁻¹ +
        (C * Z + D)⁻¹ * C := by
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have hadj : (Z * Cᴴ + Dᴴ) * W = Z * Aᴴ + Bᴴ :=
    _root_.GlobalTheory.SW.HAct.den'_act h1 h2 h3 h4 hdet0
  have hinv : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hadj]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3]
    abel
  have hunit : IsUnit (C' * W + D').det := isUnit_iff_ne_zero.mpr hdet1
  have hC : (C * Z + D)⁻¹ * C = (C * Z + D)⁻¹ * (C' * W + D')⁻¹ * ((C' * W + D') * C) := by
    rw [Matrix.mul_assoc ((C * Z + D)⁻¹), ← Matrix.mul_assoc ((C' * W + D')⁻¹),
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rw [hinv, Matrix.mul_inv_rev, hC]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem matrix_of_apply_row {m r : Type} {α : Type} (f : m → r → α) (k : m) :
    Matrix.of f k = f k := rfl

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in

theorem _root_.GlobalTheory.SW.transH_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (γ γ' : _root_.GlobalTheory.SW.M2 E N), γ ∈ _root_.GlobalTheory.SW.UU E N → γ' ∈ _root_.GlobalTheory.SW.UU E N → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' = _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) * _root_.GlobalTheory.SW.hFac Ψ γ Z z z') ∧ ∀ φ ψ χ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.TransH Ψ γ φ ψ → _root_.GlobalTheory.SW.TransH Ψ γ' ψ χ → _root_.GlobalTheory.SW.TransH Ψ (γ' * γ) φ χ := by
  intro E _ _ _ Ψ n N γ γ' hγ hγ'
  have key : ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N,
      _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' =
        _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z)
          (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
          (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) *
        _root_.GlobalTheory.SW.hFac Ψ γ Z z z' := by
    intro Z hZ z z'
    obtain ⟨hτ, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    obtain ⟨-, hden, -⟩ := hcomp γ' hγ'
    have hτ' := ((_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ' hγ').2 _ hmem).1
    unfold _root_.GlobalTheory.SW.hFac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hlow := (_root_.GlobalTheory.SW.HAct.mul_blocks (E := E) (τ : E →+* ℂ) γ γ').2.2.1
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks (by
      rw [← _root_.GlobalTheory.SW.HAct.map_blocks (E := E) (τ : E →+* ℂ) γ]
      exact _root_.GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) hγ)
    have hM := inv_denominator_mul_lower_left_cocycle (C' := (toBlocks₂₁ γ').map (τ : E →+* ℂ))
      (D' := (toBlocks₂₂ γ').map (τ : E →+* ℂ)) (Z := Z τ) h1 h2 h3 h4 (hτ τ).1 (hτ' τ).1
    rw [hden τ, Matrix.det_mul, mul_pow, hlow]
    simp only [_root_.GlobalTheory.SW.hDen, _root_.GlobalTheory.SW.hDen',
      _root_.GlobalTheory.SW.hAct] at hM ⊢
    rw [hM]
    simp only [matrix_of_apply_row, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_add,
      Complex.exp_add]
    ring
  refine ⟨key, fun φ ψ χ hφ hψ Z hZ z z' => ?_⟩
  obtain ⟨-, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hact, hden, hadj⟩ := hcomp γ' hγ'
  have hvar : (fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ (γ' * γ) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ *ᵥ
          (Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) k := by
    funext τ
    congr 1
    funext k
    rw [hadj τ, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rfl
  have hvar' : (fun τ => Matrix.of fun k =>
        z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ (γ' * γ) Z τ)⁻¹) =
      fun τ => Matrix.of fun k =>
        (Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) k ᵥ*
          (_root_.GlobalTheory.SW.hDen Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ := by
    funext τ
    congr 1
    funext k
    rw [hden τ, Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul]
    rfl
  rw [hact, hvar, hvar', hψ _ hmem, hφ Z hZ z z', key Z hZ z z', mul_assoc]
