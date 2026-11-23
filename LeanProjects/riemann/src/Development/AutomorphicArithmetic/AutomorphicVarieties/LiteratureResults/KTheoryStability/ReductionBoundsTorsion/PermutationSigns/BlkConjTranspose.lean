import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open Classical

namespace PositivityTheory.KB.BlockInvariants.ComplexBlocks

section Mat

variable {ι : Type} [Fintype ι] {q : ℕ}

def fT' (A : Matrix (Fin q → ι) (Fin q → ι) ℂ) (B : Fin q → Matrix ι ι ℂ) : ℂ :=
  ∑ I, ∑ J, A I J * ∏ i, B i (I i) (J i)

theorem prod_sum_sum (g : Fin q → ι → ι → ℂ) :
    ∏ i, (∑ x, ∑ y, g i x y) = ∑ I : Fin q → ι, ∑ J : Fin q → ι, ∏ i, g i (I i) (J i) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Fintype.prod_sum]

theorem tp_mul (A B : Matrix ι ι ℂ) : tp q (A * B) = tp q A * tp q B := by
  ext I J
  simp only [tp, of_apply, mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

omit [Fintype ι] in
theorem tp_one [DecidableEq ι] : tp q (1 : Matrix ι ι ℂ) = 1 := by
  ext I J
  simp only [tp, of_apply, one_apply]
  by_cases h : I = J
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, I i ≠ J i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem sum4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem fT'_conj (A : Matrix (Fin q → ι) (Fin q → ι) ℂ) (P : Matrix ι ι ℂ) (B : Fin q → Matrix ι ι ℂ) :
    fT' A (fun i => P * B i * Pᴴ) = fT' (tp q Pᵀ * A * tp q (P.map star)) B := by
  have h1 : ∀ (b : Matrix ι ι ℂ) (x y : ι), (P * b * Pᴴ) x y = ∑ u, ∑ v, P x u * b u v * star (P y v) := by
    intro b x y
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  unfold fT'
  simp only [h1, prod_sum_sum, Finset.mul_sum]
  rw [sum4]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun V _ => ?_
  simp only [mul_apply, tp, of_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  simp only [Finset.prod_mul_distrib]
  ring

end Mat

section GlobalTheory

variable {W : Type} [Fintype W] {m : ℕ}

theorem blk_mul (d e : W → Matrix (Fin m) (Fin m) ℂ) : blk d * blk e = blk fun w => d w * e w := by
  ext x y
  simp only [blk, mul_apply, of_apply]
  rw [Fintype.sum_prod_type]
  simp only
  by_cases h : x.1 = y.1
  · rw [if_pos h, Finset.sum_eq_single x.1]
    · simp only [if_true, h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : x.1 = w
    · subst h1; simp [h]
    · simp [h1]

theorem blk_one : blk (fun _ : W => (1 : Matrix (Fin m) (Fin m) ℂ)) = 1 := by
  ext x y
  simp only [blk, of_apply, one_apply, Prod.ext_iff]
  by_cases h : x.1 = y.1 <;> simp [h]

theorem blk_transpose (d : W → Matrix (Fin m) (Fin m) ℂ) : (blk d)ᵀ = blk fun w => (d w)ᵀ := by
  ext x y
  simp only [blk, of_apply, transpose_apply]
  by_cases h : x.1 = y.1
  · rw [if_pos h.symm, if_pos h, h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem blk_map_star (d : W → Matrix (Fin m) (Fin m) ℂ) : (blk d).map star = blk fun w => (d w).map star := by
  ext x y
  simp only [blk, of_apply, map_apply]
  split_ifs <;> simp

theorem blk_conjTranspose (d : W → Matrix (Fin m) (Fin m) ℂ) : (blk d)ᴴ = blk fun w => (d w)ᴴ := by
  rw [conjTranspose, blk_transpose, blk_map_star]
  rfl

theorem tp_blk_supp {q : ℕ} (e : W → Matrix (Fin m) (Fin m) ℂ) (X Y : Fin q → Ix W m)
    (h : tp q (blk e) X Y ≠ 0) (i : Fin q) : (X i).1 = (Y i).1 := by
  by_contra hc
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [blk, hc]))

end GlobalTheory

section Herm

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev K (L : Type) [Field L] [NumberField L] (N : ℕ) : Type := InfinitePlace L × Fin N × Fin N × Bool

def Mm (a b : Fin N) (ε : Bool) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if ε then (if i = a ∧ j = b then Complex.I else 0) - (if i = b ∧ j = a then Complex.I else 0)
    else (if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0)

theorem Mm_herm (a b : Fin N) (ε : Bool) : (Mm a b ε).IsHermitian := by
  ext i j
  simp only [Mm, conjTranspose_apply, of_apply]
  have e1 : (j = a ∧ i = b) = (i = b ∧ j = a) := propext and_comm
  have e2 : (j = b ∧ i = a) = (i = a ∧ j = b) := propext and_comm
  simp only [e1, e2]
  cases ε <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split_ifs <;> simp [Complex.conj_I]

theorem sd1 (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    ∑ a, ∑ b, (if i = a ∧ j = b then f a b else 0) = f i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hb]
  · simp

theorem sd2 (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    ∑ a, ∑ b, (if i = b ∧ j = a then f a b else 0) = f j i := by
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hb]
  · simp

def MH (k : K L N) : HS L N :=
  mkHS (fun w => if w = k.1 then Mm k.2.1 k.2.2.1 k.2.2.2 else 0) fun w => by
    split_ifs
    · exact Mm_herm _ _ _
    · exact isHermitian_zero

def coef (k : K L N) (Y : HS L N) : ℝ :=
  if k.2.2.2 then (mat Y k.1 k.2.1 k.2.2.1).im / 2 else (mat Y k.1 k.2.1 k.2.2.1).re / 2

def c1 (ε : Bool) : ℂ := if ε then -Complex.I / 4 else 1 / 4

def c2 (ε : Bool) : ℂ := if ε then Complex.I / 4 else 1 / 4

theorem mat_expand (z : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ∑ a, ∑ b, ∑ ε, (c1 ε * z a b + c2 ε * z b a) * Mm a b ε i j = z i j := by
  simp only [Fintype.sum_bool, c1, c2, Mm, of_apply, if_true, Bool.false_eq_true, if_false, mul_add, mul_sub,
    mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, sd1, sd2]
  ring_nf
  rw [Complex.I_sq]
  ring

def gc (k : K L N) (x y : Ix (InfinitePlace L) N) : ℂ :=
  (if x = (k.1, k.2.1) ∧ y = (k.1, k.2.2.1) then c1 k.2.2.2 else 0) +
    (if x = (k.1, k.2.2.1) ∧ y = (k.1, k.2.1) then c2 k.2.2.2 else 0)

def lc (k : K L N) (B : Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) : ℂ :=
  ∑ x, ∑ y, gc k x y * B x y

theorem sum_delta (p p' : Ix (InfinitePlace L) N) (c : ℂ)
    (B : Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) :
    ∑ x, ∑ y, (if x = p ∧ y = p' then c else 0) * B x y = c * B p p' := by
  rw [Finset.sum_eq_single p, Finset.sum_eq_single p']
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; exact Finset.sum_eq_zero fun y _ => by simp [hb]
  · simp

theorem lc_eq (k : K L N) (B : Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) :
    lc k B = c1 k.2.2.2 * B (k.1, k.2.1) (k.1, k.2.2.1) + c2 k.2.2.2 * B (k.1, k.2.2.1) (k.1, k.2.1) := by
  simp only [lc, gc, add_mul, Finset.sum_add_distrib, sum_delta]

theorem blk_MH (k : K L N) (x y : Ix (InfinitePlace L) N) :
    blk (fun w => mat (MH k) w) x y = if x.1 = y.1 ∧ x.1 = k.1 then Mm k.2.1 k.2.2.1 k.2.2.2 x.2 y.2 else 0 := by
  simp only [blk, MH, mat_mkHS, of_apply]
  by_cases h : x.1 = y.1
  · rw [if_pos h]
    by_cases h' : x.1 = k.1
    · rw [if_pos h', if_pos ⟨h, h'⟩]
    · rw [if_neg h', if_neg (fun hh => h' hh.2)]; rfl
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

theorem blk_expand (Z : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) :
    blk Z = ∑ k : K L N, lc k (blk Z) • blk (fun w => mat (MH k) w) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, lc_eq, blk_MH]
  by_cases h : x.1 = y.1
  · have hb : blk Z x y = Z x.1 x.2 y.2 := by simp [blk, h]
    rw [hb, Fintype.sum_prod_type, Finset.sum_eq_single x.1]
    · simp only [true_and, if_true, h]
      simp only [blk, of_apply, if_true, Fintype.sum_prod_type]
      rw [← h]
      exact (mat_expand (Z x.1) x.2 y.2).symm
    · intro b _ hb
      exact Finset.sum_eq_zero fun r _ => by simp [Ne.symm hb]
    · simp
  · rw [show blk Z x y = 0 by simp [blk, h]]
    exact (Finset.sum_eq_zero fun r _ => by simp [h]).symm

theorem lc_herm (k : K L N) (Y : HS L N) : lc k (blk fun w => mat Y w) = (coef k Y : ℂ) := by
  rw [lc_eq]
  have hY : mat Y k.1 k.2.2.1 k.2.1 = star (mat Y k.1 k.2.1 k.2.2.1) := ((mat_herm Y k.1).apply _ _).symm
  simp only [blk, of_apply, if_true, hY, coef, c1, c2]
  apply Complex.ext <;> cases k.2.2.2 <;> simp <;> ring

theorem mat_sum {ι : Type} (s : Finset ι) (f : ι → HS L N) (w : InfinitePlace L) :
    mat (∑ i ∈ s, f i) w = ∑ i ∈ s, mat (f i) w := by
  ext a b
  simp [mat, Submodule.coe_sum, Finset.sum_apply, Matrix.sum_apply]

theorem herm_decomp (Y : HS L N) : Y = ∑ k : K L N, coef k Y • MH k := by
  refine HS_ext fun w => ?_
  ext a b
  have h := congrFun (congrFun (blk_expand (fun w => mat Y w)) (w, a)) (w, b)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, lc_herm] at h
  simp only [blk, of_apply, if_true] at h
  rw [h, mat_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.real_smul]

variable {q : ℕ}

theorem f_expand (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) (Y : Fin q → HS L N) :
    f Y = ∑ κ : Fin q → K L N, (∏ i, coef (κ i) (Y i)) * f (fun i => MH (κ i)) := by
  have : f Y = f (fun i => ∑ k : K L N, coef k (Y i) • MH k) := congrArg f (funext fun i => herm_decomp (Y i))
  rw [this, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

theorem fT'_expand (A : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (Z : Fin q → InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) :
    fT' A (fun i => blk (Z i)) =
      ∑ κ : Fin q → K L N, (∏ i, lc (κ i) (blk (Z i))) * fT' A (fun i => blk fun w => mat (MH (κ i)) w) := by
  have h : ∀ (i : Fin q) (x y : Ix (InfinitePlace L) N),
      blk (Z i) x y = ∑ k : K L N, lc k (blk (Z i)) * blk (fun w => mat (MH k) w) x y := by
    intro i x y
    conv_lhs => rw [blk_expand (Z i)]
    simp [Matrix.sum_apply]
  unfold fT'
  simp only [h, Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [sum3]
  exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => by ring

def Tm (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) :
    Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ :=
  fun I J => ∑ κ : Fin q → K L N, (∏ i, gc (κ i) (I i) (J i)) * (f (fun i => MH (κ i)) : ℂ)

theorem fT'_Tm (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ)
    (B : Fin q → Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) :
    fT' (Tm f) B = ∑ κ : Fin q → K L N, (∏ i, lc (κ i) (B i)) * (f (fun i => MH (κ i)) : ℂ) := by
  unfold fT' Tm lc
  simp only [prod_sum_sum, Finset.sum_mul]
  rw [sum3]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem fT'_Tm_herm (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) (Y : Fin q → HS L N) :
    fT' (Tm f) (fun i => blk fun w => mat (Y i) w) = (f Y : ℂ) := by
  rw [fT'_Tm, f_expand f Y]
  simp only [lc_herm]
  push_cast
  rfl

theorem Tm_supp (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) (I J : Fin q → Ix (InfinitePlace L) N)
    (h : Tm f I J ≠ 0) (i : Fin q) : (I i).1 = (J i).1 := by
  by_contra hc
  apply h
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_mul]
  have h1 : ¬(I i = ((κ i).1, (κ i).2.1) ∧ J i = ((κ i).1, (κ i).2.2.1)) := by
    rintro ⟨h1, h2⟩; exact hc (by rw [h1, h2])
  have h2 : ¬(I i = ((κ i).1, (κ i).2.2.1) ∧ J i = ((κ i).1, (κ i).2.1)) := by
    rintro ⟨h1, h2⟩; exact hc (by rw [h1, h2])
  simp only [gc, if_neg h1, if_neg h2, add_zero]

theorem conj_supp (d1 d2 : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ)
    (A : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (hA : ∀ I J, A I J ≠ 0 → ∀ i, (I i).1 = (J i).1) (X Y : Fin q → Ix (InfinitePlace L) N)
    (h : (tp q (blk d1) * A * tp q (blk d2)) X Y ≠ 0) (i : Fin q) : (X i).1 = (Y i).1 := by
  rw [mul_apply] at h
  obtain ⟨J, -, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hJ
  rw [mul_apply] at h1
  obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨h3, h4⟩ := mul_ne_zero_iff.1 hI
  rw [tp_blk_supp d1 X I h3 i, hA I J h4 i, tp_blk_supp d2 J Y h2 i]

theorem blk_E (p p' : Ix (InfinitePlace L) N) (hp : p.1 = p'.1) (x y : Ix (InfinitePlace L) N) :
    blk (fun w => if w = p.1 then Matrix.of (fun a b => if a = p.2 ∧ b = p'.2 then (1 : ℂ) else 0) else 0) x y =
      if x = p ∧ y = p' then 1 else 0 := by
  rcases x with ⟨xw, xa⟩
  rcases y with ⟨yw, ya⟩
  rcases p with ⟨pw, pa⟩
  rcases p' with ⟨pw', pa'⟩
  simp only at hp
  subst hp
  simp only [blk, of_apply, Prod.mk.injEq]
  by_cases h1 : xw = yw
  · subst h1
    by_cases h2 : xw = pw
    · subst h2; simp
    · simp [h2]
  · rw [if_neg h1, if_neg]
    rintro ⟨⟨h2, -⟩, h3, -⟩
    exact h1 (h2.trans h3.symm)

theorem fT'_E (A : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (I J : Fin q → Ix (InfinitePlace L) N) (hc : ∀ i, (I i).1 = (J i).1) :
    fT' A (fun i => blk (fun w => if w = (I i).1 then
      Matrix.of (fun a b => if a = (I i).2 ∧ b = (J i).2 then (1 : ℂ) else 0) else 0)) = A I J := by
  unfold fT'
  simp only [blk_E _ _ (hc _), Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  have e : ∀ I' J' : Fin q → Ix (InfinitePlace L) N, (∀ i, I' i = I i ∧ J' i = J i) ↔ (I' = I ∧ J' = J) := by
    intro I' J'
    simp only [funext_iff, forall_and]
  simp only [e, ite_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single I (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem uniq (A A' : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (hA : ∀ I J, A I J ≠ 0 → ∀ i, (I i).1 = (J i).1) (hA' : ∀ I J, A' I J ≠ 0 → ∀ i, (I i).1 = (J i).1)
    (h : ∀ Z : Fin q → InfinitePlace L → Matrix (Fin N) (Fin N) ℂ,
      fT' A (fun i => blk (Z i)) = fT' A' (fun i => blk (Z i))) : A = A' := by
  ext I J
  by_cases hc : ∀ i, (I i).1 = (J i).1
  · have := h fun i w => if w = (I i).1 then
      Matrix.of (fun a b => if a = (I i).2 ∧ b = (J i).2 then (1 : ℂ) else 0) else 0
    rwa [fT'_E A I J hc, fT'_E A' I J hc] at this
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have h1 : A I J = 0 := by by_contra h1; exact hi (hA I J h1 i)
    have h2 : A' I J = 0 := by by_contra h2; exact hi (hA' I J h2 i)
    rw [h1, h2]

end Herm

end PositivityTheory.KB.BlockInvariants.ComplexBlocks

namespace PositivityTheory.KB.BlockInvariants

open ComplexBlocks

theorem cplx : Cplx := by
  intro L _ _ N q f hf
  refine ⟨Tm f, fun Y => ?_, fun d hd => ?_⟩
  · show f Y = (fT' (Tm f) (fun i => blk fun w => mat (Y i) w)).re
    rw [fT'_Tm_herm, Complex.ofReal_re]
  · have hd1 : ∀ w, d w * (d w)ᴴ = 1 := fun w => by
      simpa [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.1 (hd w)
    have hd2 : ∀ w, (d w)ᴴ * d w = 1 := fun w => by
      simpa [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff'.1 (hd w)
    set d' : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun w => (d w)ᵀ with hd'
    have ct : ∀ w, (d' w)ᴴ = ((d w)ᴴ)ᵀ := fun w => by ext i j; rfl
    have hu1 : ∀ w, d' w * (d' w)ᴴ = 1 := fun w => by
      rw [ct, hd', ← transpose_mul, hd2, transpose_one]
    have hu2 : ∀ w, (d' w)ᴴ * d' w = 1 := fun w => by
      rw [ct, hd', ← transpose_mul, hd1, transpose_one]
    let u : Gp L N := fun w => ⟨d' w, (d' w)ᴴ, hu1 w, hu2 w⟩
    have hmat : ∀ (Y : HS L N) w, mat (actL u Y) w = d' w * mat Y w * (d' w)ᴴ := by
      intro Y w
      rw [mat_actL]
      simp [u, Units.inv_mk, conjTranspose_conjTranspose]
    have hone : actL u (one L N).1 = (one L N).1 := HS_ext fun w => by
      rw [hmat]
      simp [one, hu1]
    have hinv := hf u hone
    have e1 : (blk d')ᵀ = blk d := by
      rw [blk_transpose]; rfl
    have e2 : (blk d').map star = blk fun w => (d w)ᴴ := by
      rw [blk_map_star]; rfl
    have key : tp q (blk d) * Tm f * tp q (blk fun w => (d w)ᴴ) = Tm f := by
      apply uniq
      · exact conj_supp _ _ _ (Tm_supp f)
      · exact Tm_supp f
      · intro Z
        rw [fT'_expand, fT'_expand]
        refine Finset.sum_congr rfl fun κ _ => ?_
        congr 1
        rw [← e1, ← e2, ← fT'_conj, fT'_Tm_herm]
        have hb : ∀ i, blk d' * blk (fun w => mat (MH (κ i)) w) * (blk d')ᴴ =
            blk fun w => mat (actL u (MH (κ i))) w := fun i => by
          rw [blk_conjTranspose, blk_mul, blk_mul]
          congr 1
          funext w
          rw [hmat]
        simp only [hb]
        rw [fT'_Tm_herm, hinv]
    calc tp q (blk d) * Tm f
        = tp q (blk d) * Tm f * (tp q (blk fun w => (d w)ᴴ) * tp q (blk d)) := by
          rw [← tp_mul, blk_mul, show (fun w => (d w)ᴴ * d w) = fun _ => 1 from funext hd2, blk_one, tp_one,
            Matrix.mul_one]
      _ = (tp q (blk d) * Tm f * tp q (blk fun w => (d w)ᴴ)) * tp q (blk d) := by
          simp only [Matrix.mul_assoc]
      _ = Tm f * tp q (blk d) := by rw [key]

end PositivityTheory.KB.BlockInvariants

end
