import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Walk

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem walk_bound (g : (K → ℕ) → ℝ) (a₀ : ℕ) (B : ℝ) (hB : 0 ≤ B) (n : ℕ)
    (hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
      |g a - g (Function.update a b (a b - 1))| ≤ B * ((∑ k, (a k : ℝ)) + 1) ^ n) :
    ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |g a| ≤ |g (fun _ => a₀)| + B * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) := by
  suffices H : ∀ N : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∑ k, (a k - a₀) = N →
      |g a| ≤ |g (fun _ => a₀)| + B * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) from
    fun a ha => H _ a ha rfl
  intro N
  induction N with
  | zero =>
    intro a ha hN
    have hEq : a = fun _ => a₀ := by
      funext k
      have := (Finset.sum_eq_zero_iff.mp hN) k (Finset.mem_univ k)
      have := ha k
      omega
    subst hEq
    have : 0 ≤ B * ((∑ _k : K, (a₀ : ℝ)) + 1) ^ (n + 1) := by positivity
    linarith
  | succ N ih =>
    intro a ha hN
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hN.trans_ne (Nat.succ_ne_zero N))
    have hab : a₀ < a b := by omega
    set a' := Function.update a b (a b - 1) with ha'
    have ha'k : ∀ k, a₀ ≤ a' k := by
      intro k
      by_cases hk : k = b
      · subst hk; simp [a']; omega
      · simp [a', hk, ha k]
    have hsplit : ∀ c : K → ℕ, ∑ k, (c k - a₀) = (c b - a₀) + ∑ k ∈ Finset.univ.erase b, (c k - a₀) :=
      fun c => (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
    have hsplitR : ∀ c : K → ℕ, ∑ k, (c k : ℝ) = (c b : ℝ) + ∑ k ∈ Finset.univ.erase b, (c k : ℝ) :=
      fun c => (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
    have hrest : ∀ k ∈ Finset.univ.erase b, a' k = a k := by
      intro k hk
      simp [a', Finset.ne_of_mem_erase hk]
    have hN' : ∑ k, (a' k - a₀) = N := by
      rw [hsplit a', Finset.sum_congr rfl (fun k hk => by rw [hrest k hk])]
      rw [hsplit a] at hN
      simp only [a', Function.update_self]
      omega
    have hs : ∑ k, (a' k : ℝ) + 1 = ∑ k, (a k : ℝ) := by
      rw [hsplitR a', hsplitR a, Finset.sum_congr rfl (fun k hk => by rw [hrest k hk])]
      simp only [a', Function.update_self]
      rw [Nat.cast_sub (by omega : 1 ≤ a b)]
      push_cast
      ring
    have h1 := ih a' ha'k hN'
    have h2 := hstep a ha b hab
    rw [hs] at h1
    set s := ∑ k, (a k : ℝ)
    have hs0 : 0 ≤ s := Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
    have hpow : s ^ (n + 1) + (s + 1) ^ n ≤ (s + 1) ^ (n + 1) := by
      have : s ^ n ≤ (s + 1) ^ n := pow_le_pow_left₀ hs0 (by linarith) n
      rw [pow_succ, pow_succ]
      nlinarith [pow_nonneg hs0 n]
    have habs : |g a| ≤ |g a'| + |g a - g a'| := by
      have := abs_sub_abs_le_abs_sub (g a) (g a')
      linarith
    calc |g a| ≤ |g a'| + |g a - g a'| := habs
      _ ≤ (|g (fun _ => a₀)| + B * s ^ (n + 1)) + B * (s + 1) ^ n := add_le_add h1 h2
      _ = |g (fun _ => a₀)| + B * (s ^ (n + 1) + (s + 1) ^ n) := by ring
      _ ≤ |g (fun _ => a₀)| + B * (s + 1) ^ (n + 1) := by
        gcongr

end Walk

section Multilinear

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem multilinear_abs_le {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ m : Fin n → K → ℤ, |f m| ≤ M * ∏ i, ∑ k, |m i k| := by
  set E : K → K → ℤ := fun k j => if k = j then 1 else 0
  refine ⟨∑ r : Fin n → K, |f (fun i => E (r i))|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro m
  have hm : m = fun i => ∑ k, m i k • E k := by
    funext i
    exact pi_eq_sum_univ (m i)
  have hexp : f m = ∑ r : Fin n → K, (∏ i, m i (r i)) * f (fun i => E (r i)) := by
    conv_lhs => rw [hm]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rw [hexp, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  rw [abs_mul, Finset.abs_prod]
  refine (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
  exact Finset.single_le_sum (f := fun k => |m i k|) (fun k _ => abs_nonneg _) (Finset.mem_univ _)

end Multilinear

section Expansion

variable {K : Type*} [Fintype K] [DecidableEq K]

def ofPositionAdditive {n : ℕ} (L : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      L (Function.update bs j (x + y)) = L (Function.update bs j x) + L (Function.update bs j y)) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun := L
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun y => L (Function.update m i y)) (hadd m i)
    exact φ.map_zsmul c x

omit [Fintype K] [DecidableEq K] in
theorem ofPositionAdditive_apply {n : ℕ} (L : (Fin n → K → ℤ) → ℤ) (hadd) (m : Fin n → K → ℤ) :
    ofPositionAdditive L hadd m = L m := rfl

omit [Fintype K] [DecidableEq K] in

theorem vecCons_const_of_ne_zero {d : ℕ} (y x : K → ℤ) (k : Fin (d + 1)) (hk : k ≠ 0) :
    Matrix.vecCons y (fun _ : Fin d => x) k = x := by
  obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr hk
  simp

omit [Fintype K] [DecidableEq K] in

theorem multilinear_step {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => K → ℤ) ℤ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 1) → K → ℤ), f (m ∘ σ) = f m)
    (x e : K → ℤ) :
    f (fun _ => x) - f (fun _ => x - e) - ((d + 1 : ℕ) : ℤ) * f (Matrix.vecCons e fun _ : Fin d => x) =
      -∑ s ∈ Finset.univ.filter (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
        f (s.piecewise (fun _ => x) (fun _ => -e)) := by
  have hadd : f (fun _ => x - e) = ∑ s : Finset (Fin (d + 1)), f (s.piecewise (fun _ => x) (fun _ => -e)) := by
    rw [← MultilinearMap.map_add_univ]
    congr 1

  have hone : ∀ s : Finset (Fin (d + 1)), s.card = d →
      f (s.piecewise (fun _ => x) (fun _ => -e)) = -f (Matrix.vecCons e fun _ : Fin d => x) := by
    intro s hs
    obtain ⟨j, hj⟩ : ∃ j, j ∉ s := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have : s = Finset.univ := Finset.eq_univ_of_forall hne
      rw [this, Finset.card_univ, Fintype.card_fin] at hs
      omega
    have hsj : s = Finset.univ.erase j := by
      refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
      · exact Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hi), Finset.mem_univ _⟩
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, hs]
        omega
    have hpw : s.piecewise (fun _ => x) (fun _ => -e) =
        (Matrix.vecCons (-e) fun _ : Fin d => x) ∘ (Equiv.swap 0 j) := by
      funext i
      simp only [Function.comp]
      by_cases hij : i = j
      · subst hij
        rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Equiv.swap_apply_right]
        simp
      · have hi : i ∈ s := by rw [hsj]; exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
        rw [Finset.piecewise_eq_of_mem _ _ _ hi]
        refine (vecCons_const_of_ne_zero _ _ _ ?_).symm
        intro h0
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
        exact hij h0
    rw [hpw, hsym]
    have hupd : (Matrix.vecCons (-e) fun _ : Fin d => x) =
        Function.update (Matrix.vecCons e fun _ : Fin d => x) 0 (-e) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp
    rw [hupd, MultilinearMap.map_update_neg]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hadd, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun s : Finset (Fin (d + 1)) => ¬ s.card + 2 ≤ d + 1)
      (fun s => s.card = d + 1)]
  have hA : ((Finset.univ.filter fun s : Finset (Fin (d + 1)) => ¬ s.card + 2 ≤ d + 1).filter
      fun s => s.card = d + 1) = {Finset.univ} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Finset.eq_univ_of_card s (by rw [h, Fintype.card_fin])
    · rintro rfl
      simp
  have hB : ((Finset.univ.filter fun s : Finset (Fin (d + 1)) => ¬ s.card + 2 ≤ d + 1).filter
      fun s => ¬ s.card = d + 1) = Finset.powersetCard d Finset.univ := by
    ext s
    have hle : s.card ≤ d + 1 := by simpa using Finset.card_le_univ s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    omega
  rw [hA, hB, Finset.sum_singleton, Finset.piecewise_univ,
    Finset.sum_congr rfl (fun s hs => hone s (Finset.mem_powersetCard.mp hs).2), Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_succ_self_right]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem multilinear_step_le {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => K → ℤ) ℤ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 1) → K → ℤ), f (m ∘ σ) = f m) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ (a : K → ℕ) (b : K),
      |f (fun _ => fun k => (a k : ℤ)) - f (fun _ => (fun k => (a k : ℤ)) - unitDeg b) -
          ((d + 1 : ℕ) : ℤ) * f (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ))| ≤
        M * ((∑ k, (a k : ℤ)) + 1) ^ (d - 1) := by
  obtain ⟨M₀, hM₀, hbd⟩ := multilinear_abs_le f
  refine ⟨(Fintype.card (Finset (Fin (d + 1))) : ℤ) * M₀, by positivity, ?_⟩
  intro a b
  set S : ℤ := ∑ k, (a k : ℤ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  rw [multilinear_step f hsym, abs_neg]
  have hterm : ∀ s ∈ Finset.univ.filter (fun s : Finset (Fin (d + 1)) => s.card + 2 ≤ d + 1),
      |f (s.piecewise (fun _ => fun k => (a k : ℤ)) (fun _ => -unitDeg b))| ≤ M₀ * (S + 1) ^ (d - 1) := by
    intro s hs
    have hcard : s.card ≤ d - 1 := by
      have := (Finset.mem_filter.mp hs).2
      omega
    refine (hbd _).trans (mul_le_mul_of_nonneg_left ?_ hM₀)
    have hprod : (∏ i, ∑ k, |(s.piecewise (fun _ => fun k => (a k : ℤ)) (fun _ => -unitDeg b)) i k|) =
        ∏ i, (if i ∈ s then S else 1) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi, if_pos hi]
        exact Finset.sum_congr rfl (fun k _ => abs_of_nonneg (Nat.cast_nonneg _))
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, if_neg hi]
        simp [unitDeg, Pi.single_apply, apply_ite]
    rw [hprod, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    calc S ^ s.card ≤ (S + 1) ^ s.card := pow_le_pow_left₀ hS (by linarith) _
      _ ≤ (S + 1) ^ (d - 1) := pow_le_pow_right₀ (by linarith) hcard
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast (Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ)

end Expansion

theorem int_eq_of_abs_sub_le {z₁ z₂ : ℤ} {c s : ℝ} (hs : 0 ≤ s) (hc : |c| < s + 1)
    (h : |(z₁ : ℝ) - (z₂ : ℝ)| ≤ c * (s + 1) ^ (((0 : ℕ) : ℝ) - 1)) : z₁ = z₂ := by
  rw [Nat.cast_zero, zero_sub, Real.rpow_neg_one] at h
  rw [← sub_eq_zero]
  set z := z₁ - z₂
  have hz : (z : ℝ) = (z₁ : ℝ) - (z₂ : ℝ) := by push_cast [z]; rfl
  rw [← hz] at h
  have hpos : 0 < s + 1 := by linarith
  have h1 : c * (s + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    exact lt_of_le_of_lt (le_abs_self c) hc
  have h2 : |(z : ℝ)| < 1 := lt_of_le_of_lt h h1
  rw [← Int.cast_abs] at h2
  have h3 : |z| < 1 := by exact_mod_cast h2
  exact Int.abs_lt_one_iff.mp h3

theorem hilbertPrime_succ (d : ℕ) (hM : MixedNumberPolynomial.Statement.{u})
    (hI : HilbertIncrement.Statement.{u}) (hmod : HilbertModule.AtDim.{u, u} d) :
    HilbertPrime.AtDim.{u} (d + 1) := by
  intro F _ K _ _ ι _ q hq hdim
  obtain ⟨hsym, hadd⟩ := hM F K ι q (d + 1) hq hdim
  obtain ⟨M, hM0, hE⟩ := multilinear_step_le (ofPositionAdditive (intNum F q) hadd) hsym
  simp only [ofPositionAdditive_apply] at hE
  choose A C hAC using hI d hmod F K ι q hq hdim
  set Cs : ℝ := ∑ b, |C b| with hCs
  set a₀ : ℕ := ∑ b, A b + ⌈Cs⌉₊ with ha₀
  set g : (K → ℕ) → ℝ := fun a => (hilbFn q (fun k => (a k : ℤ)) : ℝ) -
    (intNum F q (fun _ : Fin (d + 1) => fun k => (a k : ℤ)) : ℝ) / ((d + 1).factorial : ℝ) with hg
  have hAb : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, ∀ k, A b ≤ a k := by
    intro a ha b k
    refine le_trans ?_ (ha k)
    exact le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (A j)) (Finset.mem_univ b))
      (Nat.le_add_right _ _)
  have hCb : ∀ b, |C b| ≤ (a₀ : ℝ) := by
    intro b
    calc |C b| ≤ Cs := Finset.single_le_sum (f := fun b => |C b|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ b)
      _ ≤ (⌈Cs⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (a₀ : ℝ) := by exact_mod_cast Nat.le_add_left _ _
  have hs0 : ∀ a : K → ℕ, 0 ≤ ∑ k, (a k : ℝ) := fun a => Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  have key : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
      g a - g (Function.update a b (a b - 1)) =
        ((((hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) : ℤ) : ℝ) -
          (intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) /
            d.factorial) -
        ((intNum F q (fun _ : Fin (d + 1) => fun k => (a k : ℤ)) -
            intNum F q (fun _ : Fin (d + 1) => (fun k => (a k : ℤ)) - unitDeg b) -
            ((d + 1 : ℕ) : ℤ) * intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) :
              ℤ) : ℝ) / ((d + 1).factorial : ℝ)) := by
    intro a ha b hb
    have hcast : (fun k => ((Function.update a b (a b - 1) k : ℕ) : ℤ)) =
        (fun k => (a k : ℤ)) - unitDeg b := by
      funext k
      by_cases hk : k = b
      · subst hk
        simp only [Function.update_self, Pi.sub_apply, unitDeg, Pi.single_eq_same]
        omega
      · simp [unitDeg, hk]
    have gfun : ∀ (c : K → ℕ) (y : K → ℤ), (fun k => (c k : ℤ)) = y →
        g c = (hilbFn q y : ℝ) - (intNum F q (fun _ : Fin (d + 1) => y) : ℝ) / ((d + 1).factorial : ℝ) := by
      intro c y h
      subst h
      rfl
    rw [gfun _ _ hcast, gfun a _ rfl]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  cases d with
  | zero =>
    have hempty : (Finset.univ.filter fun s : Finset (Fin (0 + 1)) => s.card + 2 ≤ 0 + 1) = ∅ := by
      ext s
      simp
    have hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
        |g a - g (Function.update a b (a b - 1))| ≤ 0 * ((∑ k, (a k : ℝ)) + 1) ^ 0 := by
      intro a ha b hb
      have hR := multilinear_step (ofPositionAdditive (intNum F q) hadd) hsym (fun k => (a k : ℤ)) (unitDeg b)
      rw [hempty, Finset.sum_empty, neg_zero] at hR
      simp only [ofPositionAdditive_apply] at hR
      have hIb := hAC b a (hAb a ha b)
      have hlt : |C b| < (∑ k, (a k : ℝ)) + 1 := by
        have h1 : (a₀ : ℝ) < a b := by exact_mod_cast hb
        have h2 : (a b : ℝ) ≤ ∑ k, (a k : ℝ) :=
          Finset.single_le_sum (f := fun k => (a k : ℝ)) (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ b)
        linarith [hCb b]
      rw [key a ha b hb, hR]
      simp only [Nat.factorial_zero, Nat.cast_one, div_one, Int.cast_zero, zero_div, sub_zero] at hIb ⊢
      have hz := int_eq_of_abs_sub_le (hs0 a) hlt hIb
      rw [hz, sub_self]
      simp
    refine ⟨a₀, |g (fun _ => a₀)|, fun a ha => ?_⟩
    have hw := walk_bound g a₀ 0 le_rfl 0 hstep a ha
    have hexp : (((0 + 1 : ℕ) : ℝ) - 1) = 0 := by norm_num
    rw [hexp, Real.rpow_zero, mul_one]
    show |g a| ≤ _
    simpa using hw
  | succ n =>
    have hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
        |g a - g (Function.update a b (a b - 1))| ≤ (Cs + M) * ((∑ k, (a k : ℝ)) + 1) ^ n := by
      intro a ha b hb
      have hIb := hAC b a (hAb a ha b)
      have hRb := hE a b
      set s := ∑ k, (a k : ℝ) with hs
      have hexp : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_natCast] at hIb
      have hRb' : |((intNum F q (fun _ : Fin (n + 1 + 1) => fun k => (a k : ℤ)) -
            intNum F q (fun _ : Fin (n + 1 + 1) => (fun k => (a k : ℤ)) - unitDeg b) -
            ((n + 1 + 1 : ℕ) : ℤ) * intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin (n + 1) => fun k => (a k : ℤ)) :
              ℤ) : ℝ)| ≤ (M : ℝ) * (s + 1) ^ n := by
        rw [← Int.cast_abs]
        have : ((M * ((∑ k, (a k : ℤ)) + 1) ^ (n + 1 - 1) : ℤ) : ℝ) = (M : ℝ) * (s + 1) ^ n := by
          rw [hs]
          push_cast
          rfl
        rw [← this]
        exact_mod_cast hRb
      rw [key a ha b hb]
      have hpos : (1 : ℝ) ≤ ((n + 1 + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hdiv : ∀ x : ℝ, |x / ((n + 1 + 1).factorial : ℝ)| ≤ |x| := by
        intro x
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((n + 1 + 1).factorial : ℝ))]
        exact div_le_self (abs_nonneg _) hpos
      have hCb' : C b * (s + 1) ^ n ≤ Cs * (s + 1) ^ n := by
        have hp : 0 ≤ (s + 1) ^ n := by positivity
        have : C b ≤ Cs := (le_abs_self _).trans
          (Finset.single_le_sum (f := fun b => |C b|) (fun j _ => abs_nonneg _) (Finset.mem_univ b))
        exact mul_le_mul_of_nonneg_right this hp
      refine (abs_sub _ _).trans ?_
      refine (add_le_add hIb ((hdiv _).trans hRb')).trans ?_
      linarith
    have hB : 0 ≤ Cs + (M : ℝ) := by
      have : 0 ≤ Cs := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      have : (0 : ℝ) ≤ M := by exact_mod_cast hM0
      linarith
    refine ⟨a₀, |g (fun _ => a₀)| + (Cs + M), fun a ha => ?_⟩
    have hw := walk_bound g a₀ (Cs + M) hB n hstep a ha
    have hexp : (((n + 1 + 1 : ℕ) : ℝ) - 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast]
    have h1 : (1 : ℝ) ≤ ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) := one_le_pow₀ (by linarith [hs0 a])
    have h2 : |g (fun _ => a₀)| ≤ |g (fun _ => a₀)| * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) :=
      le_mul_of_one_le_right (abs_nonneg _) h1
    show |g a| ≤ _
    nlinarith

theorem HilbertPrime.proof (hZ : HilbertDimZero.Statement.{u}) (hI : HilbertIncrement.Statement.{u})
    (hM : MixedNumberPolynomial.Statement.{u}) (hMP : ModulesFromPrimes.Statement.{u, u}) :
    HilbertPrime.Statement.{u} := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero =>
      intro F _ K _ _ ι _ q hq hdim
      obtain ⟨a₀, ha₀⟩ := hZ F K ι q hq (by simpa using hdim)
      refine ⟨a₀, 0, fun a ha => ?_⟩
      have hfun : (fun _ : Fin 0 => fun k => (a k : ℤ)) = (![] : Fin 0 → K → ℤ) :=
        Subsingleton.elim _ _
      rw [hfun, ha₀ a ha]
      simp
    | succ d =>
      exact hilbertPrime_succ d hM hI (hMP d (fun e he => ih e (by omega)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
