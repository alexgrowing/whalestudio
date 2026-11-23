import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.GaussSum

theorem twist {N W : Type} [AddCommGroup N] [Fintype N] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (Q : N → W) (B : N →+ N →+ W) (hQ : ∀ x y, Q (x + y) = Q x + Q y + B x y) (ψ : N →+ W)
    (hT : ∑ x, e (Q x) = ∑ x, e (ψ x - Q x)) :
    ∑ x, e (Q x) = 0 ∨ ∃ a, ∑ x, e (Q x) = e (Q a) * conj (∑ x, e (Q x)) := by
  by_cases hz : ∑ x, e (Q x) = 0
  · exact Or.inl hz
  right
  have hsq : (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) := by
    calc (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ x, e (ψ x - Q x) * ∑ y, e (Q y) := by
          rw [← Finset.sum_mul, ← hT]
      _ = ∑ x, ∑ z, e (Q z) * e (ψ x + B x z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Equiv.sum_comp (Equiv.addLeft x), Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← he, ← he, Equiv.coe_addLeft, hQ]
          congr 1
          abel
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
  have hne : ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) ≠ 0 := hsq ▸ mul_ne_zero hz hz
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha' := right_ne_zero_of_mul ha
  have h1 : ∀ y, e (ψ y + B y a) = 1 := by
    intro y
    have : ∑ x, e (ψ x + B x a) = e (ψ y + B y a) * ∑ x, e (ψ x + B x a) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addLeft y)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← he, Equiv.coe_addLeft]
      congr 1
      simp only [map_add, AddMonoidHom.add_apply]
      abel
    exact (mul_eq_right₀ ha').1 this.symm
  refine ⟨a, ?_⟩
  conv_lhs => rw [hT]
  rw [map_sum, ← Equiv.sum_comp (Equiv.addRight a) (fun x => conj (e (Q x))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hc, ← he, Equiv.coe_addRight, hQ, ← mul_one (e (Q a + _)), ← h1 x, ← he]
  congr 1
  abel

def quat {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) : Fin 4 → M :=
  ![a • x 0 + (-b) • x 1 + (-c) • x 2 + (-d) • x 3,
    b • x 0 + a • x 1 + (-d) • x 2 + c • x 3,
    c • x 0 + d • x 1 + a • x 2 + (-b) • x 3,
    d • x 0 + (-c) • x 1 + b • x 2 + a • x 3]

theorem quat_add {M : Type} [AddCommGroup M] (a b c d : ℤ) (x y : Fin 4 → M) :
    quat a b c d (x + y) = quat a b c d x + quat a b c d y := by
  funext i
  fin_cases i <;> simp [quat] <;> module

theorem quat_conj {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) (i : Fin 4) :
    quat a (-b) (-c) (-d) (quat a b c d x) i = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • x i := by
  fin_cases i <;> simp [quat] <;> module

theorem quat_form {M W : Type} [AddCommGroup M] [AddCommGroup W] (β : M →+ M →+ W) (a b c d : ℤ)
    (x y : Fin 4 → M) :
    ∑ i, β (quat a b c d x i) (quat a b c d y i) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • ∑ i, β (x i) (y i) := by
  simp only [Fin.sum_univ_four, quat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply]
  module

theorem pow_four {M W : Type} [AddCommGroup M] [Fintype M] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (q : M → W) (β : M →+ M →+ W) (hq : ∀ x y, q (x + y) = q x + q y + β x y) :
    (∑ x, e (q x)) ^ 4 = 0 ∨ ∃ a : Fin 4 → M,
      (∑ x, e (q x)) ^ 4 = (∏ i, e (q (a i))) * conj ((∑ x, e (q x)) ^ 4) := by
  classical
  set n := Fintype.card M with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hnx : ∀ x : M, (n : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 1)
  have hm : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (n : ℤ) - 1 := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) habcd
    push_cast [Nat.cast_sub hn1] at h
    exact h
  have hinj : Function.Injective (quat (M := M) (a : ℤ) b c d) := by
    intro x y hxy
    funext i
    have hx := quat_conj (a : ℤ) b c d x i
    have hy := quat_conj (a : ℤ) b c d y i
    rw [hm, sub_smul, hnx, one_smul, zero_sub] at hx hy
    rw [← neg_inj, ← hx, ← hy, hxy]
  have hbij := hinj.bijective_of_finite
  have hprod : ∀ y : Fin 4 → W, e (∑ i, y i) = ∏ i, e (y i) := by
    intro y; simp only [Fin.sum_univ_four, Fin.prod_univ_four, he]
  have hS4 : (∑ x, e (q x)) ^ 4 = ∑ x : Fin 4 → M, e (∑ i, q (x i)) := by
    rw [Finset.sum_pow', Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun x _ => (hprod (fun i => q (x i))).symm)
  let B : (Fin 4 → M) →+ (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ∑ i, β (x i) (y i))
      (fun y z => by simp [Finset.sum_add_distrib]))
    (fun x y => by ext z; simp [Finset.sum_add_distrib])
  have hB : ∀ x y, B x y = ∑ i, β (x i) (y i) := fun _ _ => rfl
  have hQ : ∀ x y : Fin 4 → M, ∑ i, q ((x + y) i) = ∑ i, q (x i) + ∑ i, q (y i) + B x y := by
    intro x y
    simp only [hB, Pi.add_apply, hq, Finset.sum_add_distrib]
  have hnB : ∀ x y, (n : ℤ) • B x y = 0 := by
    intro x y
    rw [← map_zsmul]
    have : (n : ℤ) • y = 0 := funext fun i => hnx (y i)
    rw [this, map_zero]
  let ψ : (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => ∑ i, q (quat (a : ℤ) b c d x i) + ∑ i, q (x i)) (by
      intro x y
      rw [quat_add, hQ, hQ, hB (quat _ _ _ _ _), quat_form, hm, ← hB, sub_smul, hnB, one_smul]
      abel)
  have := twist e he hc h0 (fun x : Fin 4 → M => ∑ i, q (x i)) B hQ ψ (by
    rw [← hbij.sum_comp (fun x => e (∑ i, q (x i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp [ψ])
  rw [← hS4] at this
  simpa only [hprod] using this

theorem isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [mul_pow, pow_mul, h, mul_comm m, pow_mul, h']; simp

theorem isMu_norm {a : ℂ} (ha : IsMu a) : ‖a‖ = 1 := by
  obtain ⟨m, hm, h⟩ := ha
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

theorem ph_sum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  intro M _ _ f ⟨h1, h3⟩
  have hmu : ∀ x, IsMu (f x) := fun x => h1 x trivial
  let u : M → Circle := fun x => ⟨f x, mem_sphere_zero_iff_norm.2 (isMu_norm (hmu x))⟩
  let p : M → Additive Circle := fun x => Additive.ofMul (u x)
  have hp : ∀ x y z, p (x + y + z) + p x + p y + p z = p (x + y) + p (y + z) + p (x + z) + p 0 := by
    intro x y z
    have : u (x + y + z) * u x * u y * u z = u (x + y) * u (y + z) * u (x + z) * u 0 :=
      Circle.ext (by simp only [Circle.coe_mul]; exact h3 x trivial y trivial z trivial)
    exact congrArg Additive.ofMul this
  let β : M →+ M →+ Additive Circle := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => p (x + y) - p x - p y + p 0)
      (fun y z => by
        have := hp x y z
        rw [← add_assoc]
        rw [← sub_eq_zero] at this ⊢; rw [← this]; abel))
    (fun x y => by
      ext1 z
      have := hp x y z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← sub_eq_zero] at this ⊢; rw [← this]; abel)
  let e : Additive Circle → ℂ := fun t => ((Additive.toMul t : Circle) : ℂ)
  have he : ∀ s t, e (s + t) = e s * e t := fun s t => by simp [e]
  have hc : ∀ t, e (-t) = conj (e t) := fun t => by
    simp only [e, toMul_neg]; exact Circle.coe_inv_eq_conj _
  have hf : ∀ x, f x = f 0 * e (p x - p 0) := by
    intro x
    have : e (p 0 + (p x - p 0)) = e (p x) := by congr 1; abel
    rw [he] at this
    exact this.symm
  have hmu' : ∀ x, IsMu (e (p x - p 0)) := by
    intro x
    rw [sub_eq_add_neg, he, hc]
    refine isMu_mul (hmu x) ?_
    obtain ⟨m, hm, h⟩ := hmu 0
    exact ⟨m, hm, by rw [← map_pow]; change conj (f 0 ^ m) = 1; rw [h, map_one]⟩
  have hsum : ∑ x, f x = f 0 * ∑ x, e (p x - p 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => hf x
  rw [hsum]
  rcases pow_four e he hc (by simp [e]) (fun x => p x - p 0) β (fun x y => by
    simp only [β, AddMonoidHom.mk'_apply]; abel) with h | ⟨a, h⟩
  · rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h, mul_zero]; exact ph_zero
  · set S := ∑ x, e (p x - p 0)
    have hz : IsMu (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) := by
      refine isMu_mul ?_ ?_
      · obtain ⟨m, hm, h⟩ := hmu 0
        exact ⟨m, hm, by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]⟩
      · rw [Fin.prod_univ_four]
        exact isMu_mul (isMu_mul (isMu_mul (hmu' _) (hmu' _)) (hmu' _)) (hmu' _)
    obtain ⟨m, hm, hz⟩ := hz
    refine ⟨8 * m, by omega, ?_⟩
    have h8 : (f 0 * S) ^ 8 = (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) * ((‖f 0 * S‖ : ℝ) : ℂ) ^ 8 := by
      have hn : ((‖S‖ : ℝ) : ℂ) ^ 8 = S ^ 4 * conj (S ^ 4) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]; push_cast; ring
      rw [norm_mul, isMu_norm (hmu 0), one_mul, hn]
      linear_combination f 0 ^ 8 * S ^ 4 * h
    rw [pow_mul, h8, mul_pow, hz, one_mul, pow_mul]

end GlobalTheory.Phase.GaussSum
