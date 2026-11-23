import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x7

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3

section Minors

variable {A : Type} [CommRing A]

theorem submatrix_mul_left {l r : ℕ} {m : Type} (e : Fin l → Fin r) (he : Function.Injective e)
    (P M : Matrix (Fin r) (Fin r) A) (f : m → Fin r)
    (h : ∀ a k, k ∉ Set.range e → P (e a) k = 0) :
    (P * M).submatrix e f = P.submatrix e e * M.submatrix e f := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective e he _ _ ?_ ?_).symm
  · intro k hk; rw [h a k hk, zero_mul]
  · intro k; rfl

theorem submatrix_mul_right {l r : ℕ} {m : Type} (e : Fin l → Fin r) (he : Function.Injective e)
    (M P : Matrix (Fin r) (Fin r) A) (f : m → Fin r)
    (h : ∀ k b, k ∉ Set.range e → P k (e b) = 0) :
    (M * P).submatrix f e = M.submatrix f e * P.submatrix e e := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective e he _ _ ?_ ?_).symm
  · intro k hk; rw [h k b hk, mul_zero]
  · intro k; rfl

theorem low_apply {r : ℕ} {L : Matrix (Fin r) (Fin r) A} (hL : IsLowUni L) {i j : Fin r} (h : i < j) :
    L i j = 0 := hL.1 (by simpa using h)

theorem up_apply {r : ℕ} {U : Matrix (Fin r) (Fin r) A} (hU : IsUpUni U) {i j : Fin r} (h : j < i) :
    U i j = 0 := hU.1 (by simpa using h)

theorem mk_low {r : ℕ} {L : Matrix (Fin r) (Fin r) A} (h : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : IsLowUni L :=
  ⟨fun i j hij => h i j (by simpa using hij), h1⟩

theorem mk_up {r : ℕ} {U : Matrix (Fin r) (Fin r) A} (h : ∀ i j, j < i → U i j = 0)
    (h1 : ∀ i, U i i = 1) : IsUpUni U :=
  ⟨fun i j hij => h i j (by simpa using hij), h1⟩

theorem not_range_castLE {l r : ℕ} (hl : l ≤ r) {k : Fin r} (hk : k ∉ Set.range (Fin.castLE hl)) :
    l ≤ k.val := by
  by_contra hlt
  exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩

theorem not_range_rev {l r : ℕ} (hl : l ≤ r) {k : Fin r}
    (hk : k ∉ Set.range (fun i : Fin l => (Fin.castLE hl i).rev)) : k.val + l < r := by
  by_contra hlt
  refine hk ⟨⟨r - 1 - k.val, by have := k.isLt; omega⟩, Fin.ext ?_⟩
  have := k.isLt
  simp only [Fin.val_rev, Fin.val_castLE]
  omega

theorem rev_inj {l r : ℕ} (hl : l ≤ r) :
    Function.Injective (fun i : Fin l => (Fin.castLE hl i).rev) := by
  intro a b h
  exact Fin.castLE_injective hl (Fin.rev_injective h)

theorem lead_invariant {r : ℕ} {L M U : Matrix (Fin r) (Fin r) A} (hL : IsLowUni L) (hU : IsUpUni U)
    (l : ℕ) (hl : l ≤ r) : lead (L * M * U) l hl = lead M l hl := by
  unfold lead
  rw [submatrix_mul_right _ (Fin.castLE_injective hl), submatrix_mul_left _ (Fin.castLE_injective hl),
    Matrix.det_mul, Matrix.det_mul]
  · have h1 : IsLowUni (L.submatrix (Fin.castLE hl) (Fin.castLE hl)) :=
      mk_low (fun i j hij => low_apply hL (by rw [Fin.lt_def] at hij ⊢; exact hij)) (fun i => hL.2 _)
    have h2 : IsUpUni (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) :=
      mk_up (fun i j hij => up_apply hU (by rw [Fin.lt_def] at hij ⊢; exact hij)) (fun i => hU.2 _)
    rw [isLowUni_det A h1, isUpUni_det A h2, one_mul, mul_one]
  · intro a k hk
    have := not_range_castLE hl hk
    exact low_apply hL (by rw [Fin.lt_def]; have := a.isLt; simp only [Fin.val_castLE]; omega)
  · intro k b hk
    have := not_range_castLE hl hk
    exact up_apply hU (by rw [Fin.lt_def]; have := b.isLt; simp only [Fin.val_castLE]; omega)

theorem corner_invariant {r : ℕ} {v₂ X v₁ : Matrix (Fin r) (Fin r) A} (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (l : ℕ) (hl : l ≤ r) : cm (v₂ * X * v₁) l hl = cm X l hl := by
  unfold cm
  rw [submatrix_mul_right _ (Fin.castLE_injective hl), submatrix_mul_left _ (rev_inj hl),
    Matrix.det_mul, Matrix.det_mul]
  · have h1 : IsLowUni (v₂.submatrix (fun i : Fin l => (Fin.castLE hl i).rev)
        (fun i : Fin l => (Fin.castLE hl i).rev)) :=
      mk_low (fun i j hij => up_apply h₂ (by
        rw [Fin.lt_def] at hij ⊢
        have := j.isLt
        simp only [Fin.val_rev, Fin.val_castLE]; omega)) (fun i => h₂.2 _)
    have h2 : IsUpUni (v₁.submatrix (Fin.castLE hl) (Fin.castLE hl)) :=
      mk_up (fun i j hij => up_apply h₁ (by rw [Fin.lt_def] at hij ⊢; exact hij)) (fun i => h₁.2 _)
    rw [isLowUni_det A h1, isUpUni_det A h2, one_mul, mul_one]
  · intro a k hk
    have := not_range_rev hl hk
    exact up_apply h₂ (by
      rw [Fin.lt_def]; have := a.isLt; simp only [Fin.val_rev, Fin.val_castLE]; omega)
  · intro k b hk
    have := not_range_castLE hl hk
    exact up_apply h₁ (by rw [Fin.lt_def]; have := b.isLt; simp only [Fin.val_castLE]; omega)

theorem lead_diagonal {r : ℕ} (d : Fin r → A) (l : ℕ) (hl : l ≤ r) :
    lead (Matrix.diagonal d) l hl = ∏ i : Fin l, d (Fin.castLE hl i) := by
  unfold lead
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl

theorem lead_ldu {r : ℕ} {L U : Matrix (Fin r) (Fin r) A} (d : Fin r → A) (hL : IsLowUni L)
    (hU : IsUpUni U) (l : ℕ) (hl : l ≤ r) :
    lead (L * Matrix.diagonal d * U) l hl = ∏ i : Fin l, d (Fin.castLE hl i) := by
  rw [lead_invariant hL hU, lead_diagonal]

theorem lead_ldu_succ {r : ℕ} {L U : Matrix (Fin r) (Fin r) A} (d : Fin r → A) (hL : IsLowUni L)
    (hU : IsUpUni U) (l : ℕ) (hl : l < r) :
    lead (L * Matrix.diagonal d * U) (l + 1) hl = d ⟨l, hl⟩ * lead (L * Matrix.diagonal d * U) l hl.le := by
  rw [lead_ldu d hL hU, lead_ldu d hL hU, Fin.prod_univ_castSucc, mul_comm]
  rfl

theorem ldu_unique {r : ℕ} {L U L' U' : Matrix (Fin r) (Fin r) A} {d d' : Fin r → A}
    (hL : IsLowUni L) (hU : IsUpUni U) (hL' : IsLowUni L') (hU' : IsUpUni U')
    (hd : lead (L * Matrix.diagonal d * U) r le_rfl ∈ nonZeroDivisors A)
    (e : L * Matrix.diagonal d * U = L' * Matrix.diagonal d' * U') : L = L' ∧ d = d' ∧ U = U' := by
  rw [lead_ldu d hL hU] at hd
  have hnz : ∀ (i : Fin r) (x : A), x * d i = 0 → x = 0 := by
    intro i x hx
    refine (mem_nonZeroDivisors_iff_right.mp hd) x ?_
    have : (∏ i : Fin r, d (Fin.castLE le_rfl i)) = d i * ∏ j ∈ Finset.univ.erase i, d j :=
      (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)).symm
    rw [this, ← mul_assoc, hx, zero_mul]
  have uL' : IsUnit L'.det := by rw [isLowUni_det A hL']; exact isUnit_one
  have uU : IsUnit U.det := by rw [isUpUni_det A hU]; exact isUnit_one
  have hP : IsLowUni (L'⁻¹ * L) := isLowUni_mul A (isLowUni_inv A hL') hL
  have hQ : IsUpUni (U' * U⁻¹) := isUpUni_mul A hU' (isUpUni_inv A hU)
  have key : (L'⁻¹ * L) * Matrix.diagonal d = Matrix.diagonal d' * (U' * U⁻¹) := by
    have h1 : L'⁻¹ * (L * Matrix.diagonal d * U) * U⁻¹ = L'⁻¹ * (L' * Matrix.diagonal d' * U') * U⁻¹ := by
      rw [e]
    have h2 : L'⁻¹ * (L * Matrix.diagonal d * U) * U⁻¹ = (L'⁻¹ * L) * Matrix.diagonal d := by
      rw [Matrix.mul_assoc L'⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ uU, Matrix.mul_assoc]
    have h3 : L'⁻¹ * (L' * Matrix.diagonal d' * U') * U⁻¹ = Matrix.diagonal d' * (U' * U⁻¹) := by
      rw [Matrix.mul_assoc L', Matrix.nonsing_inv_mul_cancel_left _ _ uL', Matrix.mul_assoc]
    rw [← h2, h1, h3]
  have ent : ∀ i j, (L'⁻¹ * L) i j * d j = d' i * (U' * U⁻¹) i j := by
    intro i j
    have := congrFun (congrFun key i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have hdd : d = d' := by
    funext i
    have := ent i i
    rwa [hP.2, hQ.2, one_mul, mul_one] at this
  have hP1 : L'⁻¹ * L = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [low_apply hP h, Matrix.one_apply_ne h.ne]
    · subst h; rw [hP.2, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h.ne']
      refine hnz j _ ?_
      rw [ent, up_apply hQ h, mul_zero]
  have hQ1 : U' * U⁻¹ = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne]
      refine hnz i _ ?_
      rw [mul_comm, hdd, ← ent, low_apply hP h, zero_mul]
    · subst h; rw [hQ.2, Matrix.one_apply_eq]
    · rw [up_apply hQ h, Matrix.one_apply_ne h.ne']
  refine ⟨?_, hdd, ?_⟩
  · have := congrArg (L' * ·) hP1
    simpa [Matrix.mul_nonsing_inv_cancel_left _ _ uL'] using this
  · have := congrArg (· * U) hQ1
    simpa [Matrix.nonsing_inv_mul_cancel_right _ _ uU] using this.symm

end Minors

section Border

variable {A : Type} [CommRing A]

def border {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A) (c : A) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) A :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => A) (Fin.lastCases (motive := fun _ => A) c u j)
      (fun i' => Fin.lastCases (motive := fun _ => A) (v i') (B i') j) i

@[simp] theorem border_cc {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A)
    (c : A) (i j : Fin r) : border B v u c i.castSucc j.castSucc = B i j := by
  simp [border]

@[simp] theorem border_cl {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A)
    (c : A) (i : Fin r) : border B v u c i.castSucc (Fin.last r) = v i := by
  simp [border]

@[simp] theorem border_lc {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A)
    (c : A) (j : Fin r) : border B v u c (Fin.last r) j.castSucc = u j := by
  simp [border]

@[simp] theorem border_ll {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A)
    (c : A) : border B v u c (Fin.last r) (Fin.last r) = c := by
  simp [border]

theorem border_eta {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    M = border (M.submatrix Fin.castSucc Fin.castSucc) (fun i => M i.castSucc (Fin.last r))
      (fun j => M (Fin.last r) j.castSucc) (M (Fin.last r) (Fin.last r)) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem border_mul {r : ℕ} (B B' : Matrix (Fin r) (Fin r) A) (v u v' u' : Fin r → A) (c c' : A) :
    border B v u c * border B' v' u' c' =
      border (B * B' + Matrix.vecMulVec v u') (B *ᵥ v' + c' • v) (u ᵥ* B' + c • u')
        (u ⬝ᵥ v' + c * c') := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.vecMulVec_apply, Matrix.mulVec,
      Matrix.vecMul, dotProduct, mul_comm]

theorem border_diagonal {r : ℕ} (d : Fin r → A) (s : A) :
    Matrix.diagonal (Fin.snoc (α := fun _ => A) d s) = border (Matrix.diagonal d) 0 0 s := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem border_low {r : ℕ} {L : Matrix (Fin r) (Fin r) A} (hL : IsLowUni L) (u : Fin r → A) :
    IsLowUni (border L 0 u 1) := by
  refine mk_low ?_ ?_
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; exact absurd h (lt_irrefl _)
    · intro h; exact absurd h (not_lt.mpr (Fin.le_last _))
    · intro _; simp
    · intro h; rw [border_cc]; exact low_apply hL (by simpa using h)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · rw [border_cc]; exact hL.2 i

theorem border_up {r : ℕ} {U : Matrix (Fin r) (Fin r) A} (hU : IsUpUni U) (v : Fin r → A) :
    IsUpUni (border U v 0 1) := by
  refine mk_up ?_ ?_
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; exact absurd h (lt_irrefl _)
    · intro _; simp
    · intro h; exact absurd h (not_lt.mpr (Fin.le_last _))
    · intro h; rw [border_cc]; exact up_apply hU (by simpa using h)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · rw [border_cc]; exact hU.2 i

theorem border_ldu {r : ℕ} (B L₀ D₀ U₀ : Matrix (Fin r) (Fin r) A) (v u : Fin r → A) (c : A)
    (uB : IsUnit B.det) (e₀ : B = L₀ * D₀ * U₀) :
    border B v u c = border L₀ 0 (u ᵥ* (B⁻¹ * L₀)) 1 *
      border D₀ 0 0 (c - ((u ᵥ* (B⁻¹ * L₀)) ᵥ* D₀) ⬝ᵥ ((U₀ * B⁻¹) *ᵥ v)) *
      border U₀ ((U₀ * B⁻¹) *ᵥ v) 0 1 := by
  have h1 : (L₀ * D₀) *ᵥ ((U₀ * B⁻¹) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← e₀, Matrix.mul_nonsing_inv _ uB,
      Matrix.one_mulVec]
  have h2 : ((u ᵥ* (B⁻¹ * L₀)) ᵥ* D₀) ᵥ* U₀ = u := by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      ← Matrix.mul_assoc L₀, ← e₀, Matrix.nonsing_inv_mul _ uB, Matrix.vecMul_one]
  rw [border_mul, border_mul]
  simp only [Matrix.zero_vecMulVec, add_zero, Matrix.mulVec_zero, smul_zero, dotProduct_zero, one_mul,
    zero_add, mul_one, h1, h2, ← e₀, add_sub_cancel]

theorem ldu_exists : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) A),
    (∀ (l : ℕ) (hl : l < r), IsUnit (lead M l hl.le)) →
    ∃ (L U : Matrix (Fin r) (Fin r) A) (d : Fin r → A), IsLowUni L ∧ IsUpUni U ∧
      M = L * Matrix.diagonal d * U := by
  intro r
  induction r with
  | zero =>
    intro M _
    exact ⟨1, 1, fun i => i.elim0, isLowUni_one A, isUpUni_one A, by ext i; exact i.elim0⟩
  | succ r ih =>
    intro M hM
    have hlead : ∀ (l : ℕ) (hl : l ≤ r), lead (M.submatrix Fin.castSucc Fin.castSucc) l hl =
        lead M l (hl.trans (Nat.le_succ r)) := by
      intro l hl; rfl
    obtain ⟨L₀, U₀, d₀, hL₀, hU₀, e₀⟩ := ih (M.submatrix Fin.castSucc Fin.castSucc)
      (fun l hl => by rw [hlead]; exact hM l (by omega))
    have uB : IsUnit (M.submatrix Fin.castSucc Fin.castSucc).det := hM r (Nat.lt_succ_self r)
    have key := border_ldu _ L₀ (Matrix.diagonal d₀) U₀ (fun i => M i.castSucc (Fin.last r))
      (fun j => M (Fin.last r) j.castSucc) (M (Fin.last r) (Fin.last r)) uB e₀
    rw [← border_eta M, ← border_diagonal] at key
    exact ⟨_, _, _, border_low hL₀ _, border_up hU₀ _, key⟩

end Border

section Blocks

variable {A : Type} [CommRing A] {r k : ℕ}

theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext a b
  simp [b11, b12, b13, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext a b
  simp [b11, b21, b22, b23, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext a b
  simp [b12, b21, b22, b23, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b11, b21, b31, b32, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b12, b22, b31, b32, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext a b
  simp [b13, b23, b31, b32, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem one_block11 : b11 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, Matrix.one_apply]

theorem one_block21 : b21 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b21]

theorem one_block31 : b31 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b31]

theorem levi_embedding_block11 (h : Matrix (Fin k) (Fin k) A) : b11 (hEmb r h) = 1 := by
  ext a b; simp [b11, hEmb]
theorem levi_embedding_block12 (h : Matrix (Fin k) (Fin k) A) : b12 (hEmb r h) = 0 := by
  ext a b; simp [b12, hEmb]
theorem levi_embedding_block13 (h : Matrix (Fin k) (Fin k) A) : b13 (hEmb r h) = 0 := by
  ext a b; simp [b13, hEmb]
theorem levi_embedding_block21 (h : Matrix (Fin k) (Fin k) A) : b21 (hEmb r h) = 0 := by
  ext a b; simp [b21, hEmb]
theorem levi_embedding_block22 (h : Matrix (Fin k) (Fin k) A) : b22 (hEmb r h) = midEmb h := by
  ext a b; simp [b22, hEmb]
theorem levi_embedding_block23 (h : Matrix (Fin k) (Fin k) A) : b23 (hEmb r h) = 0 := by
  ext a b; simp [b23, hEmb]
theorem levi_embedding_block31 (h : Matrix (Fin k) (Fin k) A) : b31 (hEmb r h) = 0 := by
  ext a b; simp [b31, hEmb]
theorem levi_embedding_block32 (h : Matrix (Fin k) (Fin k) A) : b32 (hEmb r h) = 0 := by
  ext a b; simp [b32, hEmb]
theorem levi_embedding_block33 (h : Matrix (Fin k) (Fin k) A) : b33 (hEmb r h) = 1 := by
  ext a b; simp [b33, hEmb]

theorem midEmb_det (h : Matrix (Fin k) (Fin k) A) : (midEmb h).det = h.det := by
  simp [midEmb]

theorem nu_blocks {x : Matrix (Idx r k) (Idx r k) A} (hx : IsNU x) :
    IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ IsUnit (b22 x).det := by
  obtain ⟨n, _, ⟨h11, h33, h22, h21, h31, h32⟩, ⟨h, hh, rfl⟩, rfl⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]; simpa using h11
  · rw [block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]; simpa using h33
  · rw [block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]; simp
  · rw [block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]; simp
  · rw [block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]; simp
  · rw [block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22]
    simp [midEmb_det, isUpUni_det A hh]

theorem eq_zero_of_mul {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y : Matrix n m A} (h : f * Y = 0) : Y = 0 := by
  rw [← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.mul_zero]

theorem cm_map {B : Type} [CommRing B] (f : A →+* B) (X : Matrix (Fin r) (Fin r) A) (l : ℕ)
    (hl : l ≤ r) : f (cm X l hl) = cm (X.map f) l hl := by
  unfold cm
  rw [RingHom.map_det]
  rfl

theorem cm_neg (X : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) :
    cm (-X) l hl = (-1) ^ l * cm X l hl := by
  unfold cm
  rw [Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply, Matrix.det_neg, Fintype.card_fin]

end Blocks

section Corner

variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

theorem exists_smul {ϖ : o} (hϖ : Irreducible ϖ) {m n : Type} (Z : Matrix m n o)
    (hZ : Z.map (IsLocalRing.residue o) = 0) : ∃ W : Matrix m n o, Z = ϖ • W := by
  have h : ∀ a b, ∃ w, Z a b = ϖ * w := by
    intro a b
    have h0 : IsLocalRing.residue o (Z a b) = 0 := congrFun (congrFun hZ a) b
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h0
    exact h0
  choose W hW using h
  exact ⟨Matrix.of W, by ext a b; simpa using hW a b⟩

theorem inverse_corner {ϖ : o} (hϖ : Irreducible ϖ) {r k : ℕ} (j : Matrix (Idx r k) (Idx r k) o)
    (X : Matrix (Fin r) (Fin r) o) (hj : KppO j) (hX : b31 j = ϖ • X) :
    ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧
      ((b33 j) * Y * (b11 j)).map (IsLocalRing.residue o) = -(X.map (IsLocalRing.residue o)) ∧
      ∀ (l : ℕ) (hl : l ≤ r),
        IsLocalRing.residue o (cm Y l hl) = (-1) ^ l * IsLocalRing.residue o (cm X l hl) := by
  obtain ⟨hdet, hNU⟩ := hj
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := nu_blocks hNU
  have hJI : j.map (IsLocalRing.residue o) * j⁻¹.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hIJ : j⁻¹.map (IsLocalRing.residue o) * j.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have u33 : IsUnit (b33 (j.map (IsLocalRing.residue o))).det := by
    rw [isUpUni_det _ h33]; exact isUnit_one
  have i31 : b31 (j⁻¹.map (IsLocalRing.residue o)) = 0 := by
    have := block31_mul (j.map (IsLocalRing.residue o)) (j⁻¹.map (IsLocalRing.residue o))
    rw [hJI, one_block31, h31, h32] at this
    exact eq_zero_of_mul u33 (by simpa using this.symm)
  have i21 : b21 (j⁻¹.map (IsLocalRing.residue o)) = 0 := by
    have := block21_mul (j.map (IsLocalRing.residue o)) (j⁻¹.map (IsLocalRing.residue o))
    rw [hJI, one_block21, h21, i31] at this
    exact eq_zero_of_mul h22 (by simpa using this.symm)
  have i11 : b11 (j⁻¹.map (IsLocalRing.residue o)) * b11 (j.map (IsLocalRing.residue o)) = 1 := by
    have := block11_mul (j⁻¹.map (IsLocalRing.residue o)) (j.map (IsLocalRing.residue o))
    rw [hIJ, one_block11, h21, h31] at this
    simpa using this.symm
  obtain ⟨Y, hY⟩ := exists_smul hϖ (b31 j⁻¹) i31
  obtain ⟨C, hC⟩ := exists_smul hϖ (b32 j) h32
  have e0 : X * b11 j⁻¹ + C * b21 j⁻¹ + b33 j * Y = 0 := by
    have := block31_mul j j⁻¹
    rw [Matrix.mul_nonsing_inv _ hdet, one_block31, hX, hC, hY, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, ← smul_add] at this
    ext a b
    have h0 := congrFun (congrFun this a) b
    simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0.symm).resolve_left hϖ.ne_zero
  have e1 : X.map (IsLocalRing.residue o) * b11 (j⁻¹.map (IsLocalRing.residue o)) +
      b33 (j.map (IsLocalRing.residue o)) * Y.map (IsLocalRing.residue o) = 0 := by
    have := congrArg (fun Z => Z.map (IsLocalRing.residue o)) e0
    simp only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
    have i21' : (b21 j⁻¹).map (IsLocalRing.residue o) = 0 := i21
    rw [i21', Matrix.mul_zero, add_zero] at this
    exact this
  have e2 : b33 (j.map (IsLocalRing.residue o)) * Y.map (IsLocalRing.residue o) *
      b11 (j.map (IsLocalRing.residue o)) = -(X.map (IsLocalRing.residue o)) := by
    rw [eq_neg_of_add_eq_zero_right e1, Matrix.neg_mul, Matrix.mul_assoc, i11, Matrix.mul_one]
  refine ⟨Y, hY, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul]; exact e2
  · intro l hl
    rw [cm_map, cm_map, ← cm_neg, ← e2, corner_invariant h33 h11]

end Corner

end Formalism.FourierDecayAlt.P.S3x7

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.S3x7

theorem ldu_decomposition_exists : Formalism.FourierDecayAlt.S3.LDUExists := by
  intro A _ r M hM
  obtain ⟨L, U, d, hL, hU, e⟩ := ldu_exists r M hM
  refine ⟨L, U, d, hL, hU, e, fun l hl => ?_⟩
  rw [e]
  exact lead_ldu_succ d hL hU l hl

theorem ldu_decomposition_unique : Formalism.FourierDecayAlt.S3.LDUUnique := by
  intro A _ r L U L' U' d d' hL hU hL' hU' _ hd e
  exact ldu_unique hL hU hL' hU' hd e

theorem lead_invariant_bis : Formalism.FourierDecayAlt.S3.LeadInvariant := by
  intro A _ r L M U hL hU l hl
  exact lead_invariant hL hU l hl

theorem corner_invariant_bis : Formalism.FourierDecayAlt.S3.CornerInvariant := by
  intro A _ r v₂ X v₁ h₂ h₁ l hl
  exact corner_invariant h₂ h₁ l hl

theorem inverse_corner_identity : Formalism.FourierDecayAlt.S3.InverseCorner := by
  intro o _ _ _ ϖ hϖ r k j X hj hX
  exact inverse_corner hϖ j X hj hX

end Formalism.FourierDecayAlt.P
