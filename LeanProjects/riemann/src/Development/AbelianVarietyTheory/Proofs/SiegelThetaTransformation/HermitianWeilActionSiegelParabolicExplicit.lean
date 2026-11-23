import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.QuadCocycle
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.Parab

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in
theorem exists_den {α β : Type} [Finite α] [Finite β] (x : Matrix α β E) :
    ∃ D : ℕ, 0 < D ∧ IntM (D • x) := by
  obtain ⟨D, hD, h⟩ := Dict.exists_den fun p : α × β => x p.1 p.2
  exact ⟨D, hD, fun i j => h (i, j)⟩

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma isIntegral_int_natCast {E : Type} [Field E] (k : ℕ) : IsIntegral ℤ (k : E) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma isIntegral_trace_mul_mul_ccT_of_intM {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    {M P : Matrix (Fin n) (Fin N) E} {β : Matrix (Fin N) (Fin N) E} (hM : _root_.GlobalTheory.SW.IntM M)
    (hβ : _root_.GlobalTheory.SW.IntM β) (hP : _root_.GlobalTheory.SW.IntM P) :
    IsIntegral ℤ (M * β * _root_.GlobalTheory.SW.ccT P).trace := by
  unfold _root_.GlobalTheory.SW.IntM at hM hβ hP
  unfold Matrix.trace _root_.GlobalTheory.SW.ccT
  refine IsIntegral.sum _ fun i _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  exact IsIntegral.sum _ fun j _ =>
    (IsIntegral.sum _ fun k _ => (hM i k).mul (hβ k j)).mul (_root_.GlobalTheory.SW.Base.isIntegral_cc (hP i j))

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma exists_int_sum_embeddings_eq_of_isIntegral {E : Type} [Field E] [NumberField E] (t : E) (ht : IsIntegral ℤ t) :
    ∃ m : ℤ, ∑ σ : E →+* ℂ, σ t = m := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E t) := Algebra.isIntegral_trace ht
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  refine ⟨m, ?_⟩
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := t)
  rw [← hm] at h2
  rw [← (RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp] at h2
  simpa using h2.symm

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma map_trace_mul_mul_ccT_eq_trace_conjTranspose {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (τ : E →+* ℂ) (M P : Matrix (Fin n) (Fin N) E) (β : Matrix (Fin N) (Fin N) E) :
    τ (M * β * _root_.GlobalTheory.SW.ccT P).trace = (M.map τ * β.map τ * (P.map τ)ᴴ).trace := by
  rw [← _root_.GlobalTheory.SW.HAct.map_ccT, ← Matrix.map_mul, ← Matrix.map_mul]
  simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma matrix_map_natCast_smul {E : Type} [Field E] {a b : Type} (τ : E →+* ℂ) (k : ℕ) (M : Matrix a b E) :
    ((k : E) • M).map τ = (k : ℂ) • M.map τ := by
  ext i j
  simp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma trace_quadratic_form_shift_expand {n N : ℕ} (X Y : Matrix (Fin n) (Fin N) ℂ) (Bh : Matrix (Fin N) (Fin N) ℂ)
    (hB : Bhᴴ = Bh) (r d : ℕ) :
    ((X + ((2 * r * d : ℕ) : ℂ) • Y) * Bh * (X + ((2 * r * d : ℕ) : ℂ) • Y)ᴴ).trace =
      (X * Bh * Xᴴ).trace + ((2 * (Y * ((d : ℂ) • Bh) * ((r : ℂ) • X)ᴴ).trace +
        2 * ((r : ℂ) ^ 2 * d) * (Y * ((d : ℂ) • Bh) * Yᴴ).trace) +
        star (2 * (Y * ((d : ℂ) • Bh) * ((r : ℂ) • X)ᴴ).trace +
        2 * ((r : ℂ) ^ 2 * d) * (Y * ((d : ℂ) • Bh) * Yᴴ).trace)) := by
  have ha : (X * Bh * Yᴴ).trace = star (Y * Bh * Xᴴ).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hB,
      Matrix.mul_assoc]
  have hb : star (Y * Bh * Yᴴ).trace = (Y * Bh * Yᴴ).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hB,
      Matrix.mul_assoc]
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul, star_add, star_mul', star_natCast, star_ofNat,
    star_pow, Nat.cast_mul, Nat.cast_ofNat, ha, hb, star_star]
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in

theorem _root_.GlobalTheory.SW.Parab.isSB_chiH (hΨ : _root_.GlobalTheory.SW.IsType Ψ)
    {β : Matrix (Fin N) (Fin N) E} (hβ : _root_.GlobalTheory.SW.ccT β = β) (c : ℂ)
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB fun x => c * _root_.GlobalTheory.SW.chiH Ψ β x * φ x := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨d, hd, hdβ⟩ := _root_.GlobalTheory.SW.Dict.exists_den (fun p : Fin N × Fin N => β p.1 p.2)
  have hdβ' : _root_.GlobalTheory.SW.IntM ((d : E) • β) := by
    unfold _root_.GlobalTheory.SW.IntM
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
    exact hdβ (i, j)
  have hcast : ∀ y : Matrix (Fin n) (Fin N) E,
      ((2 * R * d : ℕ) : E) • y = (R : E) • ((2 * d : ℕ) : E) • y := by
    intro y
    rw [smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨2 * R * d, by positivity, ?_, ?_⟩
  · intro x hx
    have hφx : φ x ≠ 0 := fun h0 => hx (by simp [h0])
    have := _root_.GlobalTheory.SW.Dict.intM_nsmul (2 * d) (h1 x hφx)
    convert this using 1
    rw [hcast, smul_comm, Nat.cast_smul_eq_nsmul E]
  · intro x y hy
    have hy' : _root_.GlobalTheory.SW.IntM (((2 * d : ℕ) : E) • y) := by
      rw [Nat.cast_smul_eq_nsmul E]
      exact _root_.GlobalTheory.SW.Dict.intM_nsmul _ hy
    have hper : φ (x + ((2 * R * d : ℕ) : E) • y) = φ x := by
      rw [hcast]
      exact h2 x _ hy'
    simp only [hper]
    by_cases hφx : φ x = 0
    · simp [hφx]
    congr 2
    have hRx := h1 x hφx
    set t : E := 2 * (y * ((d : E) • β) * _root_.GlobalTheory.SW.ccT ((R : E) • x)).trace +
      2 * ((R : E) ^ 2 * d) * (y * ((d : E) • β) * _root_.GlobalTheory.SW.ccT y).trace with ht
    have htI : IsIntegral ℤ t := by
      refine IsIntegral.add ?_ ?_
      · exact (by simpa using isIntegral_int_natCast (E := E) 2 : IsIntegral ℤ (2 : E)).mul
          (isIntegral_trace_mul_mul_ccT_of_intM hy hdβ' hRx)
      · exact ((by simpa using isIntegral_int_natCast (E := E) 2 : IsIntegral ℤ (2 : E)).mul
          (((isIntegral_int_natCast R).pow 2).mul (isIntegral_int_natCast d))).mul
          (isIntegral_trace_mul_mul_ccT_of_intM hy hdβ' hy)
    obtain ⟨m, hm⟩ := exists_int_sum_embeddings_eq_of_isIntegral t htI
    have hsum : ∑ τ : Ψ, τ.1 ((x + ((2 * R * d : ℕ) : E) • y) * β *
        _root_.GlobalTheory.SW.ccT (x + ((2 * R * d : ℕ) : E) • y)).trace =
        ∑ τ : Ψ, τ.1 (x * β * _root_.GlobalTheory.SW.ccT x).trace + m := by
      rw [← hm, _root_.GlobalTheory.SW.Dict.sum_type hΨ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have hBh : (β.map τ.1)ᴴ = β.map τ.1 := by
        rw [← _root_.GlobalTheory.SW.HAct.map_ccT, hβ]
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, map_trace_mul_mul_ccT_eq_trace_conjTranspose, map_trace_mul_mul_ccT_eq_trace_conjTranspose,
        Matrix.map_add _ (map_add τ.1), matrix_map_natCast_smul, trace_quadratic_form_shift_expand _ _ _ hBh R d, ht]
      simp only [map_add, map_mul, map_pow, map_natCast, map_ofNat, map_trace_mul_mul_ccT_eq_trace_conjTranspose,
        matrix_map_natCast_smul]
      simp only [Complex.star_def, map_add, map_mul, map_pow, map_natCast, map_ofNat]
    unfold _root_.GlobalTheory.SW.chiH
    rw [hsum, mul_add, Complex.exp_add]
    have hm1 : Complex.exp (2 * Real.pi * Complex.I * m) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * m = m * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [hm1, mul_one]

theorem blocks {γ : M2 E N} (hγ : γ ∈ UU E N) (h0 : γ.toBlocks₂₁ = 0) :
    ccT γ.toBlocks₁₁ * γ.toBlocks₂₂ = 1 ∧
      ccT (γ.toBlocks₁₂ * ccT γ.toBlocks₁₁) = γ.toBlocks₁₂ * ccT γ.toBlocks₁₁ := by
  have h : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := hγ
  have e : ccT γ = Matrix.fromBlocks (ccT γ.toBlocks₁₁) (ccT γ.toBlocks₂₁) (ccT γ.toBlocks₁₂)
      (ccT γ.toBlocks₂₂) := by
    ext (i | i) (j | j) <;> rfl
  rw [e] at h
  nth_rewrite 5 [← Matrix.fromBlocks_toBlocks γ] at h
  have z : ccT (0 : Matrix (Fin N) (Fin N) E) = 0 := by ext i j; simp [ccT, cc]
  rw [h0, z, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  generalize γ.toBlocks₁₁ = A at *
  generalize γ.toBlocks₁₂ = B at *
  generalize γ.toBlocks₂₂ = D at *
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj] at h2 h3 h4
  refine ⟨h2, ?_⟩
  have h5 : A * ccT D = 1 := mul_eq_one_comm.1 h3
  have h6 : D * ccT A = 1 := mul_eq_one_comm.1 h2
  have h7 : ccT D * B = ccT B * D := by rw [← sub_eq_zero, sub_eq_add_neg]; exact h4
  rw [Base.ccT_mul, Base.ccT_ccT]
  calc A * ccT B = A * (ccT B * D) * ccT A := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h6, Matrix.mul_one]
    _ = B * ccT A := by rw [← h7, ← Matrix.mul_assoc, h5, Matrix.one_mul]

end

end GlobalTheory.SW.Parab

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma isUnit_det_diag_blocks_of_lower_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {γ : _root_.GlobalTheory.SW.M2 E N} (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N) (h0 : γ.toBlocks₂₁ = 0) :
    IsUnit γ.toBlocks₁₁.det ∧ IsUnit γ.toBlocks₂₂.det := by
  have h := (_root_.GlobalTheory.SW.HAct.group_part hγ).1
  have hγ' : γ = fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ 0 γ.toBlocks₂₂ := by
    rw [← h0]
    exact (fromBlocks_toBlocks γ).symm
  rw [hγ', det_fromBlocks_zero₂₁] at h
  exact IsUnit.mul_iff.1 h

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma exists_pos_nat_smul_mul_intM_of_intM {E : Type} [Field E] [NumberField E] {n N : ℕ}
    (M : Matrix (Fin N) (Fin N) E) : ∃ d : ℕ, 0 < d ∧ ∀ x : Matrix (Fin n) (Fin N) E,
      _root_.GlobalTheory.SW.IntM x → _root_.GlobalTheory.SW.IntM (d • (x * M)) := by
  obtain ⟨d, hd, hM⟩ := _root_.GlobalTheory.SW.Dict.exists_den (fun p : Fin N × Fin N => M p.1 p.2)
  refine ⟨d, hd, fun x hx => ?_⟩
  unfold _root_.GlobalTheory.SW.IntM at hx ⊢
  intro k j
  rw [Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [← mul_smul_comm]
  exact (hx k i).mul (hM (i, j))

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma isSB_comp_mul_right_of_isUnit_det {E : Type} [Field E] [NumberField E] {n N : ℕ}
    {A : Matrix (Fin N) (Fin N) E} (hA : IsUnit A.det) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (hφ : _root_.GlobalTheory.SW.IsSB φ) : _root_.GlobalTheory.SW.IsSB fun x => φ (x * A) := by
  obtain ⟨d, hd, h1⟩ := exists_pos_nat_smul_mul_intM_of_intM (n := n) A
  obtain ⟨d', hd', h2⟩ := exists_pos_nat_smul_mul_intM_of_intM (n := n) A⁻¹
  let e : Matrix (Fin n) (Fin N) E →+ Matrix (Fin n) (Fin N) E :=
    { toFun := fun x => x * A
      map_zero' := Matrix.zero_mul A
      map_add' := fun x y => Matrix.add_mul x y A }
  refine _root_.GlobalTheory.SW.Dict.isSB_comp e d d' hd hd' h1 (fun x hx => ?_) hφ
  have := h2 _ hx
  change _root_.GlobalTheory.SW.IntM (d' • (x * A * A⁻¹)) at this
  rwa [Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.mul_one] at this

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma ccT_neg_mul_ccT {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) E) :
    _root_.GlobalTheory.SW.ccT (-(B * _root_.GlobalTheory.SW.ccT A)) = -(A * _root_.GlobalTheory.SW.ccT B) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply Matrix.map_injective τ.injective
  show (_root_.GlobalTheory.SW.ccT _).map τ = τ.mapMatrix (-(A * _root_.GlobalTheory.SW.ccT B))
  rw [_root_.GlobalTheory.SW.HAct.map_ccT]
  change (τ.mapMatrix (-(B * _root_.GlobalTheory.SW.ccT A)))ᴴ = _
  simp only [map_neg, map_mul, RingHom.mapMatrix_apply, _root_.GlobalTheory.SW.HAct.map_ccT,
    conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma toBlocks₁₁_mul_ccT_toBlocks₁₂_comm_of_mem_UU {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {γ : _root_.GlobalTheory.SW.M2 E N} (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N) (h0 : γ.toBlocks₂₁ = 0) :
    γ.toBlocks₁₁ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₂ = γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply Matrix.map_injective τ.injective
  change τ.mapMatrix _ = τ.mapMatrix _
  simp only [map_mul, RingHom.mapMatrix_apply, _root_.GlobalTheory.SW.HAct.map_ccT]
  have h := _root_.GlobalTheory.SW.HAct.map_mem τ hγ
  rw [_root_.GlobalTheory.SW.HAct.map_blocks, h0] at h
  obtain ⟨_, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks h
  simp only [Matrix.map_zero _ (map_zero τ), conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    zero_add] at h2 h3
  set A := γ.toBlocks₁₁.map τ
  set B := γ.toBlocks₁₂.map τ
  set D := γ.toBlocks₂₂.map τ
  have hDA' : D * Aᴴ = 1 := mul_eq_one_comm.1 h2
  have hAD' : A * Dᴴ = 1 := mul_eq_one_comm.1 h3
  calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA', Matrix.mul_one]
    _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = A * (Dᴴ * B) * Aᴴ := by rw [h4]
    _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = B * Aᴴ := by rw [hAD', Matrix.one_mul]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {γ : _root_.GlobalTheory.SW.M2 E N} (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N)
    (h0 : γ.toBlocks₂₁ = 0) (τ : E →+* ℂ) :
    (γ.toBlocks₁₁.map τ)ᴴ * γ.toBlocks₂₂.map τ = 1 ∧ (γ.toBlocks₂₂.map τ)ᴴ * γ.toBlocks₁₁.map τ = 1 := by
  have h := _root_.GlobalTheory.SW.HAct.map_mem τ hγ
  rw [_root_.GlobalTheory.SW.HAct.map_blocks, h0] at h
  obtain ⟨_, h2, h3, _⟩ := _root_.GlobalTheory.SW.HAct.blocks h
  simp only [Matrix.map_zero _ (map_zero τ), conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add] at h2 h3
  exact ⟨h2, h3⟩

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma map_trace_mul_mul_ccT_self_eq_sum_dotProduct {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (τ : E →+* ℂ) (x : Matrix (Fin n) (Fin N) E) (β : Matrix (Fin N) (Fin N) E) :
    τ (x * β * _root_.GlobalTheory.SW.ccT x).trace =
      ∑ k, (x.map τ) k ⬝ᵥ (β.map τ) *ᵥ star ((x.map τ) k) := by
  have hc : ∀ a k, τ (_root_.GlobalTheory.SW.ccT x a k) = star (τ (x k a)) := fun a k =>
    congrFun (congrFun (_root_.GlobalTheory.SW.HAct.map_ccT τ x) a) k
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, hc, dotProduct, mulVec,
    Matrix.map_apply, Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma hermitian_parabolic_exponent_rows_eq {n N : ℕ} (Y z z' : Matrix (Fin n) (Fin N) ℂ) (A B D Z : Matrix (Fin N) (Fin N) ℂ)
    (hAD : Aᴴ * D = 1) (hDA : Dᴴ * A = 1) (k : Fin n) :
    ((Y * Dᴴ) k ⬝ᵥ (-(B * Aᴴ)) *ᵥ star ((Y * Dᴴ) k)) +
      (((Y * Dᴴ) k ⬝ᵥ ((A * Z + B) * D⁻¹) *ᵥ star ((Y * Dᴴ) k)) + (Y * Dᴴ) k ⬝ᵥ (Dᴴ)⁻¹ *ᵥ z k +
        (z' k ᵥ* D⁻¹) ⬝ᵥ star ((Y * Dᴴ) k)) =
      Y k ⬝ᵥ Z *ᵥ star (Y k) + Y k ⬝ᵥ z k + z' k ⬝ᵥ star (Y k) := by
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_left_inv hAD
  have hDHinv : (Dᴴ)⁻¹ = A := Matrix.inv_eq_right_inv hDA
  have hrow : (Y * Dᴴ) k = Y k ᵥ* Dᴴ := rfl
  have hstar : star ((Y * Dᴴ) k) = D *ᵥ star (Y k) := by
    rw [hrow, Matrix.star_vecMul, conjTranspose_conjTranspose]
  rw [hstar, hrow, hDinv, hDHinv]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have e1 : Dᴴ * -(B * Aᴴ) * D = -(Dᴴ * B) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, hAD, Matrix.mul_one]
  have e2 : Dᴴ * ((A * Z + B) * Aᴴ) * D = Z + Dᴴ * B := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hAD, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc, hDA,
      Matrix.one_mul]
  rw [e1, e2, hDA, hAD]
  simp only [Matrix.vecMul_one, Matrix.vecMul_add, Matrix.vecMul_neg, add_dotProduct,
    neg_dotProduct]
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma transH_chiH_mul_comp_of_toBlocks₂₁_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} {n N : ℕ} {γ : _root_.GlobalTheory.SW.M2 E N}
    (hγ : γ ∈ _root_.GlobalTheory.SW.UU E N) (h0 : γ.toBlocks₂₁ = 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    _root_.GlobalTheory.SW.TransH Ψ γ φ (fun x => (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) *
      _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x *
        φ (x * γ.toBlocks₁₁)) := by
  have hdetA : IsUnit γ.toBlocks₁₁.det := by
    have h := (_root_.GlobalTheory.SW.HAct.group_part hγ).1
    have hγ' : γ = fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ 0 γ.toBlocks₂₂ := by
      rw [← h0]
      exact (fromBlocks_toBlocks γ).symm
    rw [hγ', det_fromBlocks_zero₂₁] at h
    exact (IsUnit.mul_iff.1 h).1
  set A := γ.toBlocks₁₁ with hA
  set B := γ.toBlocks₁₂ with hB
  set D := γ.toBlocks₂₂ with hD
  let e : Matrix (Fin n) (Fin N) E ≃ Matrix (Fin n) (Fin N) E :=
    { toFun := fun y => y * A⁻¹
      invFun := fun x => x * A
      left_inv := fun y => by simp only [Matrix.mul_assoc, nonsing_inv_mul _ hdetA, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, mul_nonsing_inv _ hdetA, Matrix.mul_one] }
  have hden : ∀ (Z : _root_.GlobalTheory.SW.CM Ψ N N) (τ : Ψ),
      _root_.GlobalTheory.SW.hDen Ψ γ Z τ = D.map τ := by
    intro Z τ
    unfold _root_.GlobalTheory.SW.hDen
    rw [h0, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_add]
  have hadj : ∀ (Z : _root_.GlobalTheory.SW.CM Ψ N N) (τ : Ψ),
      _root_.GlobalTheory.SW.hDen' Ψ γ Z τ = (D.map τ)ᴴ := by
    intro Z τ
    unfold _root_.GlobalTheory.SW.hDen'
    rw [h0, Matrix.map_zero _ (map_zero _), conjTranspose_zero, Matrix.mul_zero, zero_add]
  have hAinv : ∀ τ : E →+* ℂ, (A⁻¹).map τ = (D.map τ)ᴴ := by
    intro τ
    have h1 : A.map τ * (A⁻¹).map τ = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hdetA, Matrix.map_one _ (map_zero τ) (map_one τ)]
    rw [← Matrix.inv_eq_right_inv h1, Matrix.inv_eq_left_inv (map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one hγ h0 τ).2]
  intro Z _ z z'
  unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.hFac
  rw [← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  have hyA : e y * A = y := e.left_inv y
  have hkey : _root_.GlobalTheory.SW.chiH Ψ (-(B * _root_.GlobalTheory.SW.ccT A)) (e y) *
      Complex.exp (2 * Real.pi * Complex.I * _root_.GlobalTheory.SW.expo Ψ (e y)
        (_root_.GlobalTheory.SW.hAct Ψ γ Z)
        (fun τ ↦ of fun k ↦ (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
        (fun τ ↦ of fun k ↦ z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹)) =
      Complex.exp (2 * Real.pi * Complex.I * _root_.GlobalTheory.SW.expo Ψ y Z z z') := by
    unfold _root_.GlobalTheory.SW.chiH _root_.GlobalTheory.SW.expo _root_.GlobalTheory.SW.hAct
    rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_trace_mul_mul_ccT_self_eq_sum_dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hey : (e y).map τ.1 = y.map τ.1 * (D.map τ.1)ᴴ := by
      change (y * A⁻¹).map τ.1 = _
      rw [Matrix.map_mul, hAinv]
    have hβ : (-(B * _root_.GlobalTheory.SW.ccT A)).map τ.1 = -(B.map τ.1 * (A.map τ.1)ᴴ) := by
      change τ.1.mapMatrix (-(B * _root_.GlobalTheory.SW.ccT A)) = _
      rw [map_neg, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        _root_.GlobalTheory.SW.HAct.map_ccT]
    simp only [of_apply, hadj, hden]
    have := hermitian_parabolic_exponent_rows_eq (y.map τ.1) (z τ) (z' τ) (A.map τ.1) (B.map τ.1) (D.map τ.1) (Z τ)
      (map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one hγ h0 τ.1).1 (map_toBlocks₁₁_conjTranspose_mul_toBlocks₂₂_eq_one hγ h0 τ.1).2 k
    rw [← hey, ← hβ] at this
    exact this
  rw [← hkey]
  simp only [hden, h0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero,
    Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [hyA]
  have hdet : ∀ τ : Ψ, (D.map τ).det = τ.1 D.det := fun τ => by
    rw [RingHom.map_det]
    rfl
  simp only [hdet]
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma toBlocks₂₁_mul_inv_eq_zero_of_botSpan_eq {E : Type} [Field E] {N : ℕ} {γ γ' : _root_.GlobalTheory.SW.M2 E N}
    (hdet : IsUnit (Matrix.det γ)) (hspan : _root_.GlobalTheory.SW.botSpan γ = _root_.GlobalTheory.SW.botSpan γ') :
    (γ' * γ⁻¹ : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) E).toBlocks₂₁ = 0 := by
  ext a j
  have hmem : γ' (Sum.inr a) ∈ _root_.GlobalTheory.SW.botSpan γ := by
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  unfold _root_.GlobalTheory.SW.botSpan at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hid : ∀ b, ∑ m, γ (Sum.inr b) m * γ⁻¹ m (Sum.inl j) = 0 := by
    intro b
    have := congrFun (congrFun (mul_nonsing_inv (γ : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) E) hdet) (Sum.inr b)) (Sum.inl j)
    rw [Matrix.mul_apply] at this
    rw [this]
    simp
  simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, Matrix.mul_apply, ← hc, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hid, mul_zero, Finset.sum_const_zero]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private lemma hFac_eq_prod_det_pow_of_toBlocks₂₁_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} {n N : ℕ} {γ : _root_.GlobalTheory.SW.M2 E N} (h0 : γ.toBlocks₂₁ = 0)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (z z' : _root_.GlobalTheory.SW.CM Ψ n N) :
    _root_.GlobalTheory.SW.hFac Ψ γ Z z z' = ∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n := by
  unfold _root_.GlobalTheory.SW.hFac _root_.GlobalTheory.SW.hDen
  simp only [h0, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_add, Matrix.mul_zero, Matrix.zero_mulVec,
    dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  rfl

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in

theorem _root_.GlobalTheory.SW.weil_parabolic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ → (∀ γ ∈ _root_.GlobalTheory.SW.UU E N, γ.toBlocks₂₁ = 0 → ∀ x, _root_.GlobalTheory.SW.weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ _root_.GlobalTheory.SW.UU E N, ∀ γ' ∈ _root_.GlobalTheory.SW.UU E N, _root_.GlobalTheory.SW.botSpan γ = _root_.GlobalTheory.SW.botSpan γ' → ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z', _root_.GlobalTheory.SW.eisTerm Ψ γ φ Z z z' = _root_.GlobalTheory.SW.eisTerm Ψ γ' φ Z z z' := by
  intro E _ _ _ Ψ hΨ n N hn φ hφ
  have hpar : ∀ γ ∈ _root_.GlobalTheory.SW.UU E N, γ.toBlocks₂₁ = 0 →
      ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ → ∀ x,
        _root_.GlobalTheory.SW.weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) *
          _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x *
            φ (x * γ.toBlocks₁₁) := by
    intro γ hγ h0 φ hφ x
    have hA := (isUnit_det_diag_blocks_of_lower_zero hγ h0).1
    have hSB : _root_.GlobalTheory.SW.IsSB fun x => (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) *
        _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x *
          φ (x * γ.toBlocks₁₁) := by
      refine _root_.GlobalTheory.SW.Parab.isSB_chiH hΨ ?_ _
        (isSB_comp_mul_right_of_isUnit_det hA hφ)
      rw [ccT_neg_mul_ccT, toBlocks₁₁_mul_ccT_toBlocks₁₂_comm_of_mem_UU hγ h0]
    have := (_root_.GlobalTheory.SW.weil_action E Ψ hΨ n N hn γ hγ φ hφ).2.2.1 _ hSB
      (transH_chiH_mul_comp_of_toBlocks₂₁_eq_zero hγ h0 φ)
    exact (congrFun this x).symm
  refine ⟨fun γ hγ h0 x => hpar γ hγ h0 φ hφ x, ?_⟩
  intro γ hγ γ' hγ' hspan Z hZ z z'
  have hprops := _root_.GlobalTheory.SW.HAct.group_part hγ
  set p := γ' * γ⁻¹ with hp
  have hpU : p ∈ _root_.GlobalTheory.SW.UU E N := _root_.GlobalTheory.SW.HAct.mul_mem hprops.2.1 hγ'
  have hp0 : p.toBlocks₂₁ = 0 := toBlocks₂₁_mul_inv_eq_zero_of_botSpan_eq hprops.1 hspan
  have hγ'eq : γ' = p * γ := by
    rw [hp, Matrix.mul_assoc, nonsing_inv_mul _ hprops.1, Matrix.mul_one]
  have htest := _root_.GlobalTheory.SW.weil_action E Ψ hΨ n N hn γ hγ φ hφ
  have hcomp := htest.2.2.2.2.2.1 p hpU
  have hcoc := (_root_.GlobalTheory.SW.transH_comp E Ψ n N γ p hγ hpU).1 Z hZ z z'
  have hD := (isUnit_det_diag_blocks_of_lower_zero hpU hp0).2
  have hc : (∏ τ : Ψ, τ.1 p.toBlocks₂₂.det ^ n) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro τ _
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hD.ne_zero)
  have hchi : _root_.GlobalTheory.SW.chiH Ψ (-(p.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT p.toBlocks₁₁))
      (0 : Matrix (Fin n) (Fin N) E) = 1 := by
    unfold _root_.GlobalTheory.SW.chiH
    simp
  unfold _root_.GlobalTheory.SW.eisTerm
  rw [hγ'eq, hcomp, hpar p hpU hp0 _ htest.1, hcoc, hFac_eq_prod_det_pow_of_toBlocks₂₁_eq_zero hp0, hchi,
    Matrix.zero_mul, mul_inv, mul_one]
  field_simp
