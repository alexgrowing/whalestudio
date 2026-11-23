import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LkDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EulerianNumeratorThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim

open Formalism.ConjugateSelfDual Finset UpperTheory.V.Sd

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have h1 : ZMod.dft (χ : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar :=
    funext fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h1, ZMod.dft_mul_const (fun k => χ⁻¹ (-k)), ZMod.dft_comp_neg (fun k => χ⁻¹ k)] at h2
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h2
  have h3 := hi.fourierTransform_eq_inv_mul_gaussSum 1
  rw [inv_inv] at h3
  have h4 : ZMod.dft (fun k => χ⁻¹ k) 1 = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := h3
  rw [h4] at h2
  rw [← h2]; ring

section
variable {l : ℕ} [hl : Fact l.Prime]

private theorem root_le {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

private theorem nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  have : ‖((n : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 h)
  simpa using this

private theorem nat_eq {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 h

private theorem nadd_le {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

private theorem mul_le {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

private theorem mul_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy

private theorem sum_le {I : Type} (s : Finset I) (f : I → Qbar l) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  Finset.sum_induction f (fun x => ‖x‖ ≤ 1) (fun _ _ => nadd_le) (by simp) h

private theorem sum_lt {I : Type} (s : Finset I) (f : I → Qbar l) (h : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 :=
  Finset.sum_induction f (fun x => ‖x‖ < 1) (fun _ _ => add_lt) (by simp) h

private def intO (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := mul_le
  one_mem' := by simp
  add_mem' := nadd_le
  zero_mem' := by simp
  neg_mem' := by simp

private theorem root_sub_one {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have h1 : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact nadd_le (root_le hl.out.ne_zero h).le (by simp)
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out (⟨x - 1, h1⟩ : intO l) 1
  have h2 := congrArg (fun z : intO l => (z : Qbar l)) hr
  simp only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul, Subring.coe_one, sub_add_cancel, h, one_pow,
    Subring.coe_natCast, mul_one] at h2
  have h3 : (x - 1) ^ l = -((l : Qbar l) * (x - 1) * r) := by linear_combination -h2
  have h4 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, h3, norm_neg]
    exact mul_lt (mul_lt (nat_lt dvd_rfl) h1) r.2
  exact lt_of_pow_lt_pow_left₀ l zero_le_one (by rwa [one_pow])

private theorem char_le (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    refine (root_le (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_).le
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one]; simp
  · rw [χ.map_nonunit ha]; simp

private theorem add_pow_N {N : ℕ} [NeZero N] (a : ZMod N) : (ZMod.stdAddChar a : ℂ) ^ N = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]; simp

private theorem gauss_le (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ‖ι.symm (gaussSum χ ZMod.stdAddChar)‖ ≤ 1 := by
  rw [gaussSum, map_sum]
  refine sum_le _ _ fun a _ => ?_
  rw [map_mul]
  refine mul_le (char_le ι χ a) (root_le (NeZero.ne N) ?_).le
  rw [← map_pow, add_pow_N, map_one]

private theorem gauss_eq (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hN : ¬ l ∣ N) : ‖ι.symm (gaussSum χ⁻¹ ZMod.stdAddChar)‖ = 1 := by
  have h := congrArg (fun z => ‖ι.symm z‖) (gauss_mul_gauss_inv χ hχ)
  simp only [map_mul, map_natCast, nat_eq hN] at h
  refine le_antisymm (gauss_le ι _) (not_lt.1 fun hlt => ?_)
  rw [mul_comm (ι.symm (gaussSum χ _))] at h
  exact (mul_lt (mul_lt hlt (gauss_le ι _)) (char_le ι χ _)).ne h

private theorem map_Lk (ι : Qbar l ≃+* ℂ) (k : ℕ) (x : ℂ) : ι.symm (Lk k x) = Lk k (ι.symm x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (ι.symm.toRingHom.toIntAlgHom) x (numL k)).symm

private theorem Lk_le (h2 : l ≠ 2) (ι : Qbar l ≃+* ℂ) {N : ℕ} (hN0 : 0 < N) (hN : ¬ l ∣ N) {k : ℕ} (hk : 1 ≤ k) {x : ℂ}
    (hx : x ^ N = 1) : ‖ι.symm (Lk k x)‖ ≤ 1 := by
  by_cases h1 : x = 1
  · subst h1
    simp [Lk, zero_pow (Nat.one_le_iff_ne_zero.1 hk)]
  · rw [map_Lk]
    refine (lkSep l h2 N hN0 hN).1 k _ (by rw [← map_pow, hx, map_one]) fun h => h1 ?_
    exact ι.symm.injective (by rw [h, map_one])

end

private theorem sum_zmod {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : ∑ a : ZMod N, f a = ∑ n ∈ range N, f n := by
  symm
  refine Finset.sum_bij' (fun n _ => (n : ZMod N)) (fun a _ => a.val) (by simp) (fun a _ => by simp [ZMod.val_lt])
    (fun n hn => ZMod.val_cast_of_lt (mem_range.1 hn)) (fun a _ => ZMod.natCast_zmod_val a) (fun _ _ => rfl)

private theorem sum_mul_range (M w : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ range (M * w), f n = ∑ j ∈ range w, ∑ b ∈ range M, f (b + M * j) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp only [add_comm (M * w)]

private theorem sum_multiples (M w : ℕ) (hw : 0 < w) (f : ℕ → ℂ) :
    ∑ n ∈ range (M * w), (if w ∣ n then f n else 0) = ∑ j ∈ range M, f (w * j) := by
  rw [mul_comm, sum_mul_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [if_neg]
    intro h
    exact hb0 (Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_left (dvd_mul_right w j)).1 h) (mem_range.1 hb))
  · intro h; exact absurd (mem_range.2 hw) h

private theorem sum_all {M w k : ℕ} (hM : 1 < M) (hw : 0 < w) (hk : 1 ≤ k) (ψ : DirichletCharacter ℂ M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (M * w)) :
    ∑ n ∈ range (M * w), ψ n * Lk k (ζ ^ n) = (w : ℂ) ^ k * ∑ b ∈ range M, ψ b * Lk k (ζ ^ (w * b)) := by
  rw [sum_mul_range, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have h1 : IsPrimitiveRoot (ζ ^ M) w := hζ.pow (by positivity) rfl
  have h2 : ∀ j, ψ ((b + M * j : ℕ) : ZMod M) = ψ b := fun j => by simp
  simp only [h2]
  by_cases hb0 : b = 0
  · subst hb0
    haveI : Fact (1 < M) := ⟨hM⟩
    simp [ψ.map_zero]
  have h3 : (ζ ^ b) ^ w ≠ 1 := by
    rw [← pow_mul, Ne, hζ.pow_eq_one_iff_dvd]
    intro h
    exact hb0 (Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mul_dvd_mul_right hw h) (mem_range.1 hb))
  have h4 := lkDist w k hw hk _ _ h1 h3
  simp only [← pow_mul, ← pow_add] at h4
  rw [← Finset.mul_sum, h4, mul_comm b w]; ring

theorem UpperTheory.V.Sd.constSmall :
    UpperTheory.V.Sd.ConstSmall := by
  intro l hl ι M w _ φ θ χ h k hk c hc
  have hw0 : 0 < w := h.prime.pos
  have hM0 : 0 < M := zero_lt_one.trans h.one_lt
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI : Fact w.Prime := ⟨h.prime⟩
  have hlw : ¬ l ∣ w := fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_sub_iff_right hw0 hd).1 h.dvd))
  have hlN : ¬ l ∣ M * w := fun hd => (hl.out.dvd_mul.1 hd).elim h.cop hlw
  set ζ : ℂ := ZMod.stdAddChar (1 : ZMod (M * w)) with hζdef
  have hζn : ∀ n : ℕ, (ZMod.stdAddChar (n : ZMod (M * w)) : ℂ) = ζ ^ n := fun n => by
    rw [hζdef, ← AddChar.map_nsmul_eq_pow]; simp
  have hζ : IsPrimitiveRoot ζ (M * w) := by
    refine ⟨add_pow_N _, fun n hn => ?_⟩
    rw [← hζn, (ZMod.isPrimitive_stdAddChar (M * w)).zmod_char_eq_one_iff] at hn
    exact (ZMod.natCast_eq_zero_iff _ _).1 hn
  have hL : ∀ n : ℕ, ‖ι.symm (Lk k (ζ ^ n))‖ ≤ 1 := fun n =>
    Lk_le h.odd ι (by positivity) hlN hk (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  have hmul : ∀ n : ℕ, χ⁻¹ (n : ZMod (M * w)) = φ⁻¹ (n : ZMod M) * θ⁻¹ (n : ZMod w) := fun n => by
    simp only [MulChar.inv_apply_eq_inv', h.mul, mul_inv]
  have hφw : φ⁻¹ (w : ZMod M) = 1 := by rw [MulChar.inv_apply_eq_inv', h.φw, inv_one]
  set T : ℂ := ∑ b ∈ range M, φ⁻¹ (b : ZMod M) * Lk k (ζ ^ (w * b)) with hT
  have hT1 : ‖ι.symm T‖ ≤ 1 := by
    rw [hT, map_sum]
    exact sum_le _ _ fun b _ => by rw [map_mul]; exact mul_le (char_le ι _ _) (hL _)
  have hA := sum_all h.one_lt hw0 hk φ⁻¹ hζ
  have hB := sum_multiples M w hw0 (fun n => φ⁻¹ (n : ZMod M) * Lk k (ζ ^ n))
  simp only [Nat.cast_mul, map_mul, hφw, one_mul] at hB
  rw [← hT] at hA hB
  have hS : ∑ a : ZMod (M * w), χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ) =
      ∑ n ∈ range (M * w), (if w ∣ n then 0 else (θ⁻¹ (n : ZMod w) - 1) * (φ⁻¹ (n : ZMod M) * Lk k (ζ ^ n))) +
        ((w : ℂ) ^ k - 1) * T := by
    rw [sub_mul, one_mul, ← hA, ← hB, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, sum_zmod]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hmul, hζn]
    split_ifs with hn
    · rw [(ZMod.natCast_eq_zero_iff _ _).2 hn, MulChar.map_zero]; ring
    · ring
  have hw1 : ‖ι.symm ((w : ℂ) ^ k - 1)‖ < 1 := by
    have h1 : l ∣ w ^ k - 1 := h.dvd.trans (Nat.sub_one_dvd_pow_sub_one w k)
    have h2 : ((w : ℂ) ^ k - 1) = ((w ^ k - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hw0)]; simp
    rw [h2, map_natCast]; exact nat_lt h1
  have hSlt : ‖ι.symm (∑ a : ZMod (M * w), χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ))‖ < 1 := by
    rw [hS, map_add, map_mul, map_sum]
    refine add_lt (sum_lt _ _ fun n _ => ?_) (mul_lt hw1 hT1)
    split_ifs with hn
    · simp
    · rw [map_mul, map_mul, map_sub, map_one]
      refine mul_lt (root_sub_one ?_) (mul_le (char_le ι _ _) (hL _))
      have hu : IsUnit (n : ZMod w) := Ne.isUnit (mt (ZMod.natCast_eq_zero_iff _ _).1 hn)
      rw [← map_pow, ← MulChar.pow_apply' _ hl.out.ne_zero, inv_pow, h.θpow, inv_one, MulChar.one_apply hu, map_one]
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    have : ¬ l ∣ 2 := fun hd => h.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 hd)
    simpa using nat_eq (l := l) this
  rw [← hc, map_mul, map_mul, norm_mul, norm_mul, gauss_eq ι χ (ePrim l M w φ θ χ h) hlN, map_ofNat, h2] at hSlt
  simpa using hSlt
