import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open Matrix

namespace GlobalTheory.EisBL.NilAlg

variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def blk (X : Matrix n n B) : Matrix (n ⊕ n) (n ⊕ n) B := fromBlocks (1 + X) (-X) X (1 - X)

theorem blk_mul (X Y : Matrix n n B) : blk X * blk Y = blk (X + Y) := by
  simp only [blk, fromBlocks_multiply]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

omit [Fintype n] in
theorem blk_zero : blk (0 : Matrix n n B) = 1 := by
  simp [blk, fromBlocks_one]

def phi (c : B →+* B) (J X : Matrix n n B) : Matrix n n B := Xᵀ * J + J * X.map c

theorem blk_map (c : B →+* B) (X : Matrix n n B) : (blk X).map c = blk (X.map c) := by
  have e : ∀ M : Matrix n n B, M.map c = c.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]

theorem blk_form (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c =
      GlobalTheory.WeilM.dbl J + fromBlocks (phi c J X) (-phi c J X) (-phi c J X) (phi c J X) := by
  rw [blk_map]
  simp only [blk, phi, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add, transpose_add,
    transpose_sub, transpose_neg, transpose_one]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

theorem blk_form_iff (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c = GlobalTheory.WeilM.dbl J ↔ phi c J X = 0 := by
  rw [blk_form]
  constructor
  · intro h
    rw [GlobalTheory.WeilM.dbl, fromBlocks_add, fromBlocks_inj] at h
    simpa using h.1
  · intro h
    rw [h]
    simp

def tau (c : B →+* B) (J K X : Matrix n n B) : Matrix n n B := -(J * X.map c * K)ᵀ

theorem phi_eq_zero_iff (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1)
    (X : Matrix n n B) : phi c J X = 0 ↔ tau c J K X = X := by
  unfold phi tau
  constructor
  · intro h
    have h1 : J * X.map c * K = -Xᵀ := by
      calc J * X.map c * K = (Xᵀ * J + J * X.map c) * K - Xᵀ * (J * K) := by noncomm_ring
        _ = -Xᵀ := by rw [h, hJK]; noncomm_ring
    rw [h1, transpose_neg, transpose_transpose, neg_neg]
  · intro h
    have h1 : Xᵀ = -(J * X.map c * K) := by
      conv_lhs => rw [← h]
      rw [transpose_neg, transpose_transpose]
    rw [h1]
    calc -(J * X.map c * K) * J + J * X.map c = -(J * X.map c * (K * J)) + J * X.map c := by noncomm_ring
      _ = 0 := by rw [hKJ]; noncomm_ring

theorem tau_add (c : B →+* B) (J K X Y : Matrix n n B) : tau c J K (X + Y) = tau c J K X + tau c J K Y := by
  unfold tau
  rw [show (X + Y).map c = X.map c + Y.map c from map_add c.mapMatrix X Y, Matrix.mul_add, Matrix.add_mul,
    transpose_add, neg_add]

omit [DecidableEq n] in
theorem tau_smul (c : B →+* B) (J K : Matrix n n B) (h : B) (hh : c h = h) (X : Matrix n n B) :
    tau c J K (h • X) = h • tau c J K X := by
  unfold tau
  have : (h • X).map c = h • X.map c := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hh]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, transpose_smul, smul_neg]

theorem tau_tau (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (X : Matrix n n B) :
    tau c J K (tau c J K X) = X := by
  have hcc : (X.map c).map c = X := by ext i j; simp [hc]
  have h1 : (tau c J K X).map c = -(K * Xᵀ * J) := by
    unfold tau
    rw [Matrix.map_neg _ (map_neg c), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc, transpose_mul, transpose_mul,
      hKc, hJc]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hε, one_smul, Matrix.mul_assoc]
  show -(J * (tau c J K X).map c * K)ᵀ = X
  rw [h1]
  rw [show J * -(K * Xᵀ * J) * K = -((J * K) * Xᵀ * (J * K)) by noncomm_ring, transpose_neg, neg_neg, hJK,
    Matrix.one_mul, Matrix.mul_one, transpose_transpose]

def proj (c : B →+* B) (J K : Matrix n n B) (h : B) (X : Matrix n n B) : Matrix n n B := h • (X + tau c J K X)

theorem proj_add (c : B →+* B) (J K : Matrix n n B) (h : B) (X Y : Matrix n n B) :
    proj c J K h (X + Y) = proj c J K h X + proj c J K h Y := by
  unfold proj
  rw [tau_add, ← smul_add]
  congr 1
  abel

theorem phi_proj (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (hh : c h = h)
    (X : Matrix n n B) : phi c J (proj c J K h X) = 0 := by
  rw [phi_eq_zero_iff c hJK hKJ]
  unfold proj
  rw [tau_smul c J K h hh, tau_add, tau_tau c hc ε hε hJc hKc hJK, add_comm]

theorem proj_of_phi (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (h2 : h * 2 = 1)
    (X : Matrix n n B) (hX : phi c J X = 0) : proj c J K h X = X := by
  unfold proj
  rw [(phi_eq_zero_iff c hJK hKJ X).1 hX, ← two_smul B X, smul_smul, h2, one_smul]

theorem hKc_of (c : B →+* B) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1) (hJc : (J.map c)ᵀ = ε • J)
    (hJK : J * K = 1) (hKJ : K * J = 1) : (K.map c)ᵀ = ε • K := by
  have hm : (K.map c)ᵀ * (ε • J) = 1 := by
    rw [← hJc, ← transpose_mul, ← Matrix.map_mul, hJK, Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  calc (K.map c)ᵀ = (K.map c)ᵀ * ((ε • J) * (ε • K)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε, one_smul, hJK, Matrix.mul_one]
    _ = ((K.map c)ᵀ * (ε • J)) * (ε • K) := (Matrix.mul_assoc _ _ _).symm
    _ = ε • K := by rw [hm, Matrix.one_mul]

theorem unip_iff_blk (M : Matrix (n ⊕ n) (n ⊕ n) B) :
    ((M - 1) * Matrix.fromRows (1 : Matrix n n B) (1 : Matrix n n B) = 0 ∧
      Matrix.fromCols (1 : Matrix n n B) (-1 : Matrix n n B) * (M - 1) = 0) ↔
      ∃ X, M = blk X := by
  constructor
  · rintro ⟨h1, h2⟩
    have hM : M - 1 = fromBlocks (M - 1).toBlocks₁₁ (M - 1).toBlocks₁₂ (M - 1).toBlocks₂₁ (M - 1).toBlocks₂₂ :=
      (fromBlocks_toBlocks (M - 1)).symm
    set a := (M - 1).toBlocks₁₁
    set b := (M - 1).toBlocks₁₂
    set c := (M - 1).toBlocks₂₁
    set d := (M - 1).toBlocks₂₂
    rw [hM, fromBlocks_mul_fromRows] at h1
    rw [hM, fromCols_mul_fromBlocks] at h2
    have e1 := congrArg Matrix.toRows₁ h1
    have e2 := congrArg Matrix.toRows₂ h1
    have e3 := congrArg Matrix.toCols₁ h2
    have e4 := congrArg Matrix.toCols₂ h2
    have z1 : toRows₁ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z2 : toRows₂ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z3 : toCols₁ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    have z4 : toCols₂ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    simp only [toRows₁_fromRows, toRows₂_fromRows, toCols₁_fromCols, toCols₂_fromCols, Matrix.mul_one,
      Matrix.one_mul, Matrix.neg_mul, z1, z2, z3, z4] at e1 e2 e3 e4
    have hb : b = -a := eq_neg_of_add_eq_zero_right e1
    have hc : c = a := (sub_eq_zero.1 (by simpa [sub_eq_add_neg] using e3)).symm
    have hd : d = -a := by rw [← hc]; exact eq_neg_of_add_eq_zero_right e2
    refine ⟨a, ?_⟩
    have : M = 1 + (M - 1) := by abel
    rw [this, hM, hb, hc, hd, blk, ← fromBlocks_one, fromBlocks_add]
    simp [sub_eq_add_neg]
  · rintro ⟨X, rfl⟩
    have e : blk X - 1 = fromBlocks X (-X) X (-X) := by
      rw [blk, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      congr 1 <;> abel
    rw [e, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks]
    constructor <;> ext i j <;> (try rcases i with i | i) <;> (try rcases j with j | j) <;>
      simp [Matrix.fromRows, Matrix.fromCols, Sum.elim_inl, Sum.elim_inr] <;> rfl

theorem blk_map' {B' : Type} [CommRing B'] (f : B →+* B') (X : Matrix n n B) : (blk X).map f = blk (X.map f) := by
  have e : ∀ M : Matrix n n B, M.map f = f.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]

theorem proj_map {B' : Type} [CommRing B'] (f : B →+* B') (c : B →+* B) (c' : B' →+* B')
    (hf : ∀ x, f (c x) = c' (f x)) (J K : Matrix n n B) (h : B) (X : Matrix n n B) :
    (proj c J K h X).map f = proj c' (J.map f) (K.map f) (f h) (X.map f) := by
  have hs : ∀ (a : B) (M : Matrix n n B), (a • M).map f = f a • M.map f := by
    intro a M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
  have hcc : (X.map c).map f = (X.map f).map c' := by ext i j; simp [hf]
  unfold proj tau
  rw [hs, show (X + -(J * X.map c * K)ᵀ).map f = X.map f + (-(J * X.map c * K)ᵀ).map f from
    map_add f.mapMatrix _ _, Matrix.map_neg _ (map_neg f), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc]

end GlobalTheory.EisBL.NilAlg
