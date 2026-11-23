import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA

namespace Formalism.InvariantFactorPaths.PW

open Finset

section nat

variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]

theorem Om_nat (E : ι → ι → Module.End K W) (E' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (h : ∀ a b x, θ (E a b x) = E' a b (θ x)) (S : Finset ι) (z : ι) (q : ℕ) :
    ∀ x, θ (Om E S z q x) = Om E' S z q (θ x) := by
  induction q with
  | zero => intro x; simp [Om]
  | succ q ih =>
    intro x
    simp only [Om, LinearMap.sum_apply, map_sum, Module.End.mul_apply, ih, h]

theorem Pstep_nat (E : ι → ι → Module.End K W) (E' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (h : ∀ a b x, θ (E a b x) = E' a b (θ x)) (S : Finset ι) (z : ι) (l : ℕ) (x : W) :
    θ (Pstep E S z l x) = Pstep E' S z l (θ x) := by
  simp only [Pstep, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Om_nat E E' θ h]

theorem invariant_natural_holds : InvNat := by
  intro K W W' ι _ _ _ _ _ _ E E' θ h l L
  induction L with
  | nil => intro x; simp [InvOp]
  | cons z L ih =>
    intro x
    simp only [InvOp, Module.End.mul_apply]
    rw [Pstep_nat E E' θ h, ih]

end nat

section ring

variable {R : Type} [Ring R]

theorem der3 (x f o e f' o' e' : R) (hf : x * f = f * x + f') (ho : x * o = o * x + o')
    (he : x * e = e * x + e') :
    x * (f * o * e) = (f * o * e) * x + (f' * o * e + f * o' * e + f * o * e') := by
  calc x * (f * o * e) = (x * f) * o * e := by simp only [mul_assoc]
    _ = f * (x * o) * e + f' * o * e := by rw [hf]; simp only [add_mul, mul_assoc]
    _ = f * o * (x * e) + f * o' * e + f' * o * e := by rw [ho]; simp only [add_mul, mul_add, mul_assoc]
    _ = (f * o * e) * x + (f' * o * e + f * o' * e + f * o * e') := by
        rw [he]; simp only [mul_add, mul_assoc]; abel

end ring

section gl

variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}

theorem GlRel.sw (h : GlRel E) (a b c d : ι) :
    E a b * E c d = E c d * E a b + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) := by
  exact sub_eq_iff_eq_add'.mp (h a b c d)

theorem Om_comm_S (h : GlRel E) {S : Finset ι} {z : ι} (hz : z ∉ S) {a b : ι} (ha : a ∈ S) (hb : b ∈ S)
    (q : ℕ) : E a b * Om E S z q = Om E S z q * E a b := by
  have hbz : b ≠ z := fun e => hz (e ▸ hb)
  have haz : a ≠ z := fun e => hz (e ▸ ha)
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    have key : ∀ i, E a b * (E z i * Om E S z q * E i z) =
        E z i * Om E S z q * E i z * E a b +
          ((if i = b then E z b * Om E S z q * E a z else 0) -
            (if i = a then E z b * Om E S z q * E a z else 0)) := by
      intro i
      have ho : E a b * Om E S z q = Om E S z q * E a b + 0 := by rw [ih, add_zero]
      rw [der3 _ _ _ _ _ _ _ (h.sw a b z i) ho (h.sw a b i z)]
      congr 1
      have hza : ¬ z = a := fun e => haz e.symm
      simp only [if_neg hbz, if_neg hza]
      by_cases hia : i = a <;> by_cases hib : i = b
      · subst hia; subst hib; simp
      · subst hia; simp [hib, Ne.symm hib]
      · subst hib; simp [hia]
      · simp [hia, hib, Ne.symm hib]
    simp only [Om]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hb, if_pos ha, sub_self, add_zero]

theorem diag_comm_omega (h : GlRel E) {S : Finset ι} {z : ι} (hz : z ∉ S)
    (q : ℕ) : E z z * Om E S z q = Om E S z q * E z z := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    simp only [Om]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    have ho : E z z * Om E S z q = Om E S z q * E z z + 0 := by rw [ih, add_zero]
    rw [der3 _ _ _ _ _ _ _ (h.sw z z z i) ho (h.sw z z i z)]
    simp [hiz, Ne.symm hiz]

theorem diag_comm (h : GlRel E) {a b c : ι} (ha : a ≠ c) (hb : b ≠ c) : E c c * E a b = E a b * E c c := by
  rw [h.sw c c a b, if_neg (Ne.symm ha), if_neg hb, sub_zero, add_zero]

theorem Om_comm_out (h : GlRel E) {S : Finset ι} {z c : ι} (hc : c ∉ S) (hcz : z ≠ c)
    (q : ℕ) : E c c * Om E S z q = Om E S z q * E c c := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    simp only [Om]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hic : i ≠ c := fun e => hc (e ▸ hi)
    have ho : E c c * Om E S z q = Om E S z q * E c c + 0 := by rw [ih, add_zero]
    have hf : E c c * E z i = E z i * E c c + 0 := by rw [diag_comm h hcz hic, add_zero]
    have he : E c c * E i z = E i z * E c c + 0 := by rw [diag_comm h hic hcz, add_zero]
    rw [der3 _ _ _ _ _ _ _ hf ho he]
    simp

def Cj (E : ι → ι → Module.End K W) (S : Finset ι) (z j : ι) : Module.End K W :=
  ∑ i ∈ S, E i z * E j i - E j z * E z z + ((S.card : K) + 1) • E j z

theorem EE_comm (h : GlRel E) {z i k : ι} (hi : i ≠ z) (hk : k ≠ z) : E i z * E k z = E k z * E i z := by
  rw [h.sw i z k z, if_neg (Ne.symm hk), if_neg (Ne.symm hi), sub_zero, add_zero]

theorem sum_G (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) :
    ∑ i ∈ S, (E j i - (if i = j then E z z else 0)) * E i z = Cj E S z j := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have h1 : ∀ i ∈ S, E j i * E i z = E i z * E j i + E j z := by
    intro i _
    rw [h.sw j i i z, if_pos (rfl : i = i), if_neg (show ¬ z = j from fun e => hjz e.symm), sub_zero]
  have h2 : E z z * E j z = E j z * E z z - E j z := by
    rw [h.sw z z j z, if_neg (show ¬ z = j from fun e => hjz e.symm), if_pos (rfl : z = z), zero_sub,
      ← sub_eq_add_neg]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', if_pos hj, h2, Cj, Finset.sum_const, add_smul, one_smul]
  rw [← Nat.cast_smul_eq_nsmul K]
  abel

theorem Cj_E (h : GlRel E) {S : Finset ι} {z j k : ι} (hz : z ∉ S) (hj : j ∈ S) (hk : k ∈ S) :
    Cj E S z j * E k z = E k z * Cj E S z j + (2 : K) • (E k z * E j z) := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have hkz : k ≠ z := fun e => hz (e ▸ hk)
  have a1 : ∀ i ∈ S, E i z * E j i * E k z =
      E k z * (E i z * E j i) + (if i = k then E k z * E j z else 0) := by
    intro i hi
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    calc E i z * E j i * E k z = E i z * (E j i * E k z) := mul_assoc _ _ _
      _ = E i z * (E k z * E j i + (if i = k then E j z else 0)) := by
          rw [h.sw j i k z, if_neg (show ¬ z = j from fun e => hjz e.symm), sub_zero]
      _ = (E i z * E k z) * E j i + E i z * (if i = k then E j z else 0) := by rw [mul_add, mul_assoc]
      _ = E k z * (E i z * E j i) + (if i = k then E k z * E j z else 0) := by
          rw [EE_comm h hiz hkz, mul_assoc]
          split_ifs with hik
          · subst hik; rfl
          · rw [mul_zero]
  have a2 : E j z * E z z * E k z = E k z * (E j z * E z z) - E k z * E j z := by
    calc E j z * E z z * E k z = E j z * (E z z * E k z) := mul_assoc _ _ _
      _ = E j z * (E k z * E z z - E k z) := by
          rw [h.sw z z k z, if_neg (show ¬ z = k from fun e => hkz e.symm), if_pos (rfl : z = z), zero_sub,
            ← sub_eq_add_neg]
      _ = (E j z * E k z) * E z z - E j z * E k z := by rw [mul_sub, mul_assoc]
      _ = E k z * (E j z * E z z) - E k z * E j z := by rw [EE_comm h hjz hkz, mul_assoc]
  simp only [Cj, add_mul, sub_mul, Finset.sum_mul, smul_mul_assoc, mul_add, mul_sub, Finset.mul_sum,
    mul_smul_comm]
  rw [Finset.sum_congr rfl a1, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hk, a2, EE_comm h hjz hkz,
    two_smul]
  abel

theorem Om_rec (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) (q : ℕ) :
    E j z * Om E S z (q + 1) = Om E S z (q + 1) * E j z +
      (∑ i ∈ S, E z i * (E j z * Om E S z q - Om E S z q * E j z) * E i z + Om E S z q * Cj E S z j) := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  have key : ∀ i ∈ S, E j z * (E z i * Om E S z q * E i z) = (E z i * Om E S z q * E i z) * E j z +
      (E z i * (E j z * Om E S z q - Om E S z q * E j z) * E i z +
        Om E S z q * ((E j i - (if i = j then E z z else 0)) * E i z)) := by
    intro i hi
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    rw [der3 _ _ _ _ _ (E j z * Om E S z q - Om E S z q * E j z) 0 (h.sw j z z i) (by abel)
      (by rw [EE_comm h hjz hiz, add_zero]), if_pos rfl]
    have hc : (E j i - (if i = j then E z z else 0)) * Om E S z q =
        Om E S z q * (E j i - (if i = j then E z z else 0)) := by
      rw [sub_mul, mul_sub, Om_comm_S h hz hj hi]
      split_ifs
      · rw [diag_comm_omega h hz]
      · simp
    rw [hc, mul_zero, add_zero, mul_assoc (Om E S z q)]
    abel
  simp only [Om, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_G h hz hj]

theorem Om_E (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) (q : ℕ) :
    E j z * Om E S z (q + 1) = Om E S z (q + 1) * E j z +
      ((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z)) := by
  have hjz : j ≠ z := fun e => hz (e ▸ hj)
  induction q with
  | zero =>
    rw [Om_rec h hz hj 0]
    congr 1
    simp [Om]
  | succ q ih =>
    have hA : E j z * Om E S z (q + 1) - Om E S z (q + 1) * E j z =
        ((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z)) := sub_eq_iff_eq_add'.mpr ih
    have hX : ∀ i ∈ S, (Cj E S z j + (q : K) • E j z) * E i z =
        E i z * (Cj E S z j + (q : K) • E j z + (2 : K) • E j z) := by
      intro i hi
      have hiz : i ≠ z := fun e => hz (e ▸ hi)
      rw [add_mul, Cj_E h hz hj hi, smul_mul_assoc, EE_comm h hjz hiz, mul_add, mul_add, mul_smul_comm,
        mul_smul_comm]
      abel
    have hs : ∑ i ∈ S, E z i * (((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z))) * E i z =
        ((q : K) + 1) • (Om E S z (q + 1) * (Cj E S z j + (q : K) • E j z + (2 : K) • E j z)) := by
      simp only [Om, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      simp only [mul_assoc]
      rw [hX i hi]
    rw [Om_rec h hz hj (q + 1), hA, hs]
    congr 1
    push_cast
    simp only [mul_add, mul_smul_comm]
    module

theorem Pstep_comm (S : Finset ι) (z : ι) (l : ℕ) (X : Module.End K W)
    (hX : ∀ q, X * Om E S z q = Om E S z q * X) : X * Pstep E S z l = Pstep E S z l * X := by
  simp only [Pstep, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hX]

theorem InvOp_comm_out (h : GlRel E) (l : ℕ) (c : ι) (L : List ι) (hc : c ∉ L) :
    E c c * InvOp E l L = InvOp E l L * E c c := by
  induction L with
  | nil => simp [InvOp]
  | cons z L ih =>
    have hcz : c ≠ z := by rintro rfl; exact hc (by simp)
    have hcL : c ∉ L := fun m => hc (by simp [m])
    have hP := Pstep_comm (E := E) L.toFinset z l (E c c)
      (fun q => Om_comm_out h (by simpa using hcL) (Ne.symm hcz) q)
    simp only [InvOp]
    rw [← mul_assoc, hP, mul_assoc, ih hcL, ← mul_assoc]

theorem Om_mem {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) (S : Finset ι) (z : ι) (q : ℕ) :
    ∀ x ∈ NN, Om E S z q x ∈ NN := by
  induction q with
  | zero => intro x hx; simpa [Om] using hx
  | succ q ih =>
    intro x hx
    simp only [Om, LinearMap.sum_apply, Module.End.mul_apply]
    exact Submodule.sum_mem _ (fun i _ => hN _ _ _ (ih _ (hN _ _ _ hx)))

theorem Pstep_mem {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) (S : Finset ι) (z : ι) (l : ℕ) :
    ∀ x ∈ NN, Pstep E S z l x ∈ NN := by
  intro x hx
  simp only [Pstep, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Om_mem hN S z q x hx))

theorem Om_vanish (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {S : Finset ι} {z : ι} (hz : z ∉ S) (q : ℕ) :
    ∀ (k : ℕ), ∀ x ∈ NN, E z z x = -(k : K) • x → l < k + q → Om E S z q x = 0 := by
  induction q with
  | zero =>
    intro k x hx hk hlt
    have hx0 : x = 0 :=
      hev z (-(k : ℤ)) x hx (by push_cast; exact hk) (by rw [abs_neg, Nat.abs_cast]; omega)
    simp [Om, hx0]
  | succ q ih =>
    intro k x hx hk hlt
    simp only [Om, LinearMap.sum_apply, Module.End.mul_apply]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hiz : i ≠ z := fun e => hz (e ▸ hi)
    have hw : E z z (E i z x) = -((k + 1 : ℕ) : K) • E i z x := by
      have e1 := DFunLike.congr_fun (h.sw z z i z) x
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, if_neg (Ne.symm hiz),
        if_pos (rfl : z = z), LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e1
      rw [e1, hk, map_smul]
      push_cast
      module
    rw [ih (k + 1) (E i z x) (hN _ _ _ hx) hw (by omega), map_zero]

def cc (K : Type) [Field K] (m q : ℕ) : K :=
  ((-1 : K) ^ q * (m.factorial : K)) / (((q + m).factorial : K) * (q.factorial : K))

theorem cc_rec [CharZero K] (m q : ℕ) : cc K m q + cc K m (q + 1) * (((q : K) + 1) * ((q : K) + 1 + m)) = 0 := by
  unfold cc
  have h1 : (q + 1 + m).factorial = (q + m + 1) * (q + m).factorial := by
    rw [show q + 1 + m = q + m + 1 by omega]; exact Nat.factorial_succ _
  have h2 : (q + 1).factorial = (q + 1) * q.factorial := Nat.factorial_succ _
  have f1 : ((q + m).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((q : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have f4 : ((q : K) + m + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (q + m)
  rw [h1, h2]
  push_cast
  field_simp
  ring

theorem cc_zero [CharZero K] (m : ℕ) : cc K m 0 = 1 := by
  have : (m.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp [cc, this]

theorem Pstep_eq (S : Finset ι) (z : ι) (l : ℕ) :
    Pstep E S z l = ∑ q ∈ range (l + 1), cc K S.card q • Om E S z q := rfl

theorem E_Om_apply (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) {u : W}
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) (q : ℕ) :
    E j z (Om E S z (q + 1) u) = Om E S z (q + 1) (E j z u) +
      (((q : K) + 1) * ((q : K) + 1 + S.card)) • Om E S z q (E j z u) := by
  have h0 : ∑ i ∈ S, E i z (E j i u) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hS j hj i hi, map_zero])
  have hC : Cj E S z j u = ((S.card : K) + 1) • E j z u := by
    simp only [Cj, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply,
      LinearMap.smul_apply, hzz, map_zero, h0, sub_zero, zero_add]
  have e1 := DFunLike.congr_fun (Om_E h hz hj q) u
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hC] at e1
  rw [e1, ← add_smul, map_smul, smul_smul]
  congr 2
  ring

theorem E_Pstep_apply [CharZero K] (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) {u : W}
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) (n : ℕ) :
    E j z (Pstep E S z n u) = cc K S.card n • Om E S z n (E j z u) := by
  induction n with
  | zero =>
    rw [Pstep_eq]
    simp [Om, cc_zero]
  | succ n ih =>
    rw [Pstep_eq, Finset.sum_range_succ, ← Pstep_eq]
    simp only [LinearMap.add_apply, map_add, ih, LinearMap.smul_apply, map_smul,
      E_Om_apply h hz hj hS hzz n]
    rw [eq_neg_of_add_eq_zero_left (cc_rec (K := K) S.card n)]
    module

theorem lower_kill [CharZero K] (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {z i : ι} (hiz : i ≠ z) {y : W} (hy : y ∈ NN) (he : E i z y = 0) (hii : E i i y = 0) (hzz : E z z y = 0) :
    E z i y = 0 := by
  have hpow : ∀ k, (E z i ^ (k + 1)) y = E z i ((E z i ^ k) y) := by
    intro k; rw [pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, (E z i ^ k) y ∈ NN := by
    intro k
    induction k with
    | zero => simpa using hy
    | succ k ih => rw [hpow]; exact hN _ _ _ ih
  have sZ : E z z * E z i = E z i * E z z + E z i := by
    rw [h.sw z z z i, if_pos (rfl : z = z), if_neg hiz, sub_zero]
  have sI : E i i * E z i = E z i * E i i - E z i := by
    rw [h.sw i i z i, if_neg hiz, if_pos (rfl : i = i), zero_sub, ← sub_eq_add_neg]
  have sE : E i z * E z i = E z i * E i z + (E i i - E z z) := by
    rw [h.sw i z z i, if_pos (rfl : z = z), if_pos (rfl : i = i)]
  have wZ : ∀ k : ℕ, E z z ((E z i ^ k) y) = (k : K) • (E z i ^ k) y := by
    intro k
    induction k with
    | zero => simp [hzz]
    | succ k ih =>
      rw [hpow, ← Module.End.mul_apply (E z z), sZ, LinearMap.add_apply, Module.End.mul_apply, ih, map_smul]
      push_cast
      module
  have wI : ∀ k : ℕ, E i i ((E z i ^ k) y) = -(k : K) • (E z i ^ k) y := by
    intro k
    induction k with
    | zero => simp [hii]
    | succ k ih =>
      rw [hpow, ← Module.End.mul_apply (E i i), sI, LinearMap.sub_apply, Module.End.mul_apply, ih, map_smul]
      push_cast
      module
  have wE : ∀ k : ℕ, E i z ((E z i ^ (k + 1)) y) = -(((k : K) + 1) * (k : K)) • (E z i ^ k) y := by
    intro k
    induction k with
    | zero =>
      rw [hpow, ← Module.End.mul_apply (E i z), sE]
      simp [he, hii, hzz]
    | succ k ih =>
      rw [hpow (k + 1), ← Module.End.mul_apply (E i z), sE, LinearMap.add_apply, LinearMap.sub_apply,
        Module.End.mul_apply, ih, map_smul, wI, wZ, ← hpow]
      push_cast
      module
  have top : ∀ k : ℕ, l < k → (E z i ^ k) y = 0 := by
    intro k hk
    exact hev z (k : ℤ) _ (hmem k) (by rw [wZ k, Int.cast_natCast])
      (by rw [Nat.abs_cast]; exact_mod_cast hk)
  have down : ∀ n : ℕ, ∀ k : ℕ, k + n = l + 1 → 1 ≤ k → (E z i ^ k) y = 0 := by
    intro n
    induction n with
    | zero => intro k hk _; exact top k (by omega)
    | succ n ih =>
      intro k hk hk1
      have h1 : (E z i ^ (k + 1)) y = 0 := ih (k + 1) (by omega) (by omega)
      have h2 := wE k
      rw [h1, map_zero] at h2
      have hk0 : (k : K) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have hk2 : (k : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      exact (smul_eq_zero.mp h2.symm).resolve_left (neg_ne_zero.mpr (mul_ne_zero hk2 hk0))
  have := down l 1 (by omega) le_rfl
  simpa using this

theorem range_mem {a b : ι} (hab : a ≠ b) (x : W) :
    E a b x ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b) := Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
      (Submodule.mem_iSup_of_mem hab (LinearMap.mem_range_self _ _)))

theorem Pstep_sub_mem [CharZero K] {S : Finset ι} {z : ι} (hz : z ∉ S) (l : ℕ) (u : W) :
    Pstep E S z l u - u ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b) := by
  rw [Pstep_eq, Finset.sum_range_succ']
  simp only [LinearMap.add_apply, cc_zero, one_smul, Om, Module.End.one_apply, add_sub_cancel_right,
    LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i hi => ?_)))
  exact range_mem (E := E) (show z ≠ i from fun e => hz (e ▸ hi)) _

theorem Pstep_inv [CharZero K] (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {S : Finset ι} {z : ι} (hz : z ∉ S) {u : W} (hu : u ∈ NN)
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) :
    ∀ a ∈ insert z S, ∀ b ∈ insert z S, E a b (Pstep E S z l u) = 0 := by
  have hP : Pstep E S z l u ∈ NN := Pstep_mem hN S z l u hu
  have hSS : ∀ a ∈ S, ∀ b ∈ S, E a b (Pstep E S z l u) = 0 := by
    intro a ha b hb
    have e1 := DFunLike.congr_fun (Pstep_comm S z l (E a b) (fun q => Om_comm_S h hz ha hb q)) u
    simp only [Module.End.mul_apply, hS a ha b hb, map_zero] at e1
    exact e1
  have hZ : E z z (Pstep E S z l u) = 0 := by
    have e1 := DFunLike.congr_fun (Pstep_comm S z l (E z z) (fun q => diag_comm_omega h hz q)) u
    simp only [Module.End.mul_apply, hzz, map_zero] at e1
    exact e1
  have hJ : ∀ j ∈ S, E j z (Pstep E S z l u) = 0 := by
    intro j hj
    have hjz : j ≠ z := fun e => hz (e ▸ hj)
    have hw : E z z (E j z u) = -((1 : ℕ) : K) • E j z u := by
      have e1 := DFunLike.congr_fun (h.sw z z j z) u
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        if_neg (show ¬ z = j from fun e => hjz e.symm), if_pos (rfl : z = z), ↓reduceIte, LinearMap.zero_apply,
        zero_sub, LinearMap.neg_apply, hzz, map_zero, zero_add] at e1
      rw [e1, Nat.cast_one, neg_one_smul]
    rw [E_Pstep_apply h hz hj hS hzz l,
      Om_vanish h hN hev hz l 1 (E j z u) (hN _ _ _ hu) hw (by omega), smul_zero]
  have hne : ∀ b ∈ S, b ≠ z := fun b hb e => hz (e ▸ hb)
  intro a ha b hb
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact hZ
  · exact lower_kill h hN hev (hne b hb) hP (hJ b hb) (hSS b hb b hb) hZ
  · exact hJ a ha
  · exact hSS a ha b hb

theorem invariant_inverse_holds : InvInv := by
  intro K W ι _ _ _ _ _ E h l NN hN hev L
  induction L with
  | nil =>
    intro _ u hu _
    refine ⟨fun a ha => by simp at ha, ?_, ?_⟩
    · simpa [InvOp] using hu
    · simp [InvOp]
  | cons z L ih =>
    intro hnd u hu hdiag
    rw [List.nodup_cons] at hnd
    obtain ⟨hzL, hnd⟩ := hnd
    obtain ⟨h1, h2, h3⟩ := ih hnd u hu (fun a ha => hdiag a (List.mem_cons_of_mem _ ha))
    have hz : z ∉ L.toFinset := by simpa using hzL
    have hzz : E z z (InvOp E l L u) = 0 := by
      have e1 := DFunLike.congr_fun (InvOp_comm_out h l z L hzL) u
      simp only [Module.End.mul_apply, hdiag z (by simp), map_zero] at e1
      exact e1
    have hS : ∀ a ∈ L.toFinset, ∀ b ∈ L.toFinset, E a b (InvOp E l L u) = 0 := by
      intro a ha b hb
      exact h1 a (by simpa using ha) b (by simpa using hb)
    have key := Pstep_inv h hN hev hz h2 hS hzz
    simp only [InvOp, Module.End.mul_apply]
    refine ⟨fun a ha b hb => key a (by simpa using ha) b (by simpa using hb), Pstep_mem hN _ _ _ _ h2, ?_⟩
    have h4 := Submodule.add_mem _ (Pstep_sub_mem (E := E) hz l (InvOp E l L u)) h3
    simpa using h4

end gl

end Formalism.InvariantFactorPaths.PW
