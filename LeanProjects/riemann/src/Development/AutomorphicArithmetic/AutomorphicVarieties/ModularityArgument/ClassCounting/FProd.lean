import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

noncomputable section

namespace UpperTheory.V.ZK.Coc

variable {A K : Type} [CommRing A] [CommGroup K]

private def F (u : K → K → A) (v : K → A) : (n : ℕ) → (Fin n → K) → A
  | 0, _ => 1
  | 1, g => v (g 0)
  | n + 2, g => u (g 0) (g 1) * F u v n fun i => g i.succ.succ

private theorem F_coc (u : K → K → A) (v : K → A) (hu : ∀ a b c, u b c - u (a * b) c + u a (b * c) - u a b = 0)
    (hv : ∀ a b, v (a * b) = v a + v b) : ∀ (n : ℕ) (g : Fin (n + 1) → K),
    F u v n (fun i => g i.succ) + ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) * F u v n (Fin.contractNth j (· * ·) g) = 0
  | 0, g => by simp [F]
  | 1, g => by
    simp [F, Fin.sum_univ_two, Fin.contractNth, hv]
  | n + 2, g => by
    have ih := F_coc u v hu hv n fun i => g i.succ.succ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h2 : ∀ j : Fin (n + 1), F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := fun j => by
      rw [F]
      congr 2
      funext i
      simp only [Fin.contractNth, Fin.val_succ, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
      rfl
    have h0 : F u v (n + 2) (Fin.contractNth 0 (· * ·) g) = u (g 0 * g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h1 : F u v (n + 2) (Fin.contractNth (Fin.succ 0) (· * ·) g) =
        u (g 0) (g 1 * g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h3 : F u v (n + 2) (fun i => g i.succ) = u (g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h4 : ∑ j : Fin (n + 1), (-1 : A) ^ ((j.succ.succ : ℕ) + 1) * F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) *
          F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2, Fin.val_succ, Fin.val_succ]; ring
    rw [h4, h0, h1, h3, eq_neg_of_add_eq_zero_right ih]
    simp only [Fin.val_zero, Fin.val_succ]
    linear_combination (F u v n fun i => g i.succ.succ.succ) * hu (g 0) (g 1) (g 2)

private theorem F_ins (u : K → K → A) (v : K → A) (hs : ∀ a b, u a b = u b a) (x : K) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    ∑ i : Fin (2 * E + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1) (Fin.insertNth (α := fun _ => K) i x g) =
      F u v (2 * E) g * v x
  | 0, g => by simp [F]
  | E + 1, g => by
    obtain ⟨a, g, rfl⟩ : ∃ (a : K) (g' : Fin (2 * E + 1) → K), g = (Fin.cons a g' : Fin (2 * E + 1 + 1) → K) := ⟨_, _, (Fin.cons_self_tail (n := 2 * E + 1) g).symm⟩
    obtain ⟨b, g, rfl⟩ : ∃ (b : K) (g' : Fin (2 * E) → K), g = (Fin.cons b g' : Fin (2 * E + 1) → K) := ⟨_, _, (Fin.cons_self_tail g).symm⟩
    change ∑ i : Fin (2 * E + 1 + 1 + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1 + 2)
      (Fin.insertNth (α := fun _ => K) i x (Fin.cons a (Fin.cons b g : Fin (2 * E + 1) → K) : Fin (2 * E + 1 + 1) → K)) =
      (u a b * F u v (2 * E) g) * v x
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, mul_assoc (u a b), ← F_ins u v hs x E g, Finset.mul_sum]
    simp only [Fin.insertNth_succ_cons, Fin.insertNth_zero', F, Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.val_zero,
      Fin.val_succ, hs x a]
    rw [← add_assoc]
    refine (congrArg₂ (· + ·) (by ring : _ = (0 : A)) (Finset.sum_congr rfl fun j _ => by ring)).trans (zero_add _)

private theorem F_prod (u : K → K → A) (v : K → A) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    F u v (2 * E) g = ∏ s : Fin E, u (g ⟨2 * s, by omega⟩) (g ⟨2 * s + 1, by omega⟩)
  | 0, g => by simp [F]
  | E + 1, g => by
    rw [Fin.prod_univ_succ]
    exact congrArg (u _ _ * ·) (F_prod u v E fun i => g i.succ.succ)

private theorem ex_log [Finite K] [IsCyclic K] (q : ℕ) (ζ : K) (hζ : orderOf ζ = q) :
    ∃ (r : ℕ) (lg : K → ℤ), 0 < r ∧ (∀ a b, ((q * r : ℕ) : ℤ) ∣ lg a + lg b - lg (a * b)) ∧
      ∀ x : ℕ, ((q * r : ℕ) : ℤ) ∣ lg (ζ ^ x) - r * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := K)
  choose y hy using hg
  simp only at hy
  have hN : 0 < orderOf g := orderOf_pos g
  have hd : ∀ m n : ℕ, g ^ m = g ^ n → (orderOf g : ℤ) ∣ (m : ℤ) - n := fun m n h =>
    (pow_eq_pow_iff_modEq.1 h).symm.dvd
  set r := (orderOf g).gcd (y ζ) with hr
  have hr0 : 0 < r := Nat.gcd_pos_of_pos_left _ hN
  have hq : q * r = orderOf g := by
    rw [← hζ, ← congrArg orderOf (hy ζ), orderOf_pow, hr, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  have hb := Nat.gcd_eq_gcd_ab (orderOf g) (y ζ)
  refine ⟨r, fun a => (orderOf g).gcdB (y ζ) * y a, hr0, fun a b => ?_, fun x => ?_⟩
  · rw [hq]
    have := hd (y a + y b) (y (a * b)) (by rw [pow_add, hy, hy, hy])
    push_cast at this
    simpa [mul_sub, mul_add] using this.mul_left ((orderOf g).gcdB (y ζ))
  · rw [hq]
    have := hd (y (ζ ^ x)) (y ζ * x) (by rw [pow_mul, hy, hy])
    push_cast at this
    have h2 := (this.mul_left ((orderOf g).gcdB (y ζ))).sub (dvd_mul_right (orderOf g : ℤ) ((orderOf g).gcdA (y ζ) * x))
    refine h2.trans (dvd_of_eq ?_)
    rw [hr, hb]; ring

end UpperTheory.V.ZK.Coc

open UpperTheory.V.ZK.Coc in
theorem UpperTheory.V.ZK.sCoc : UpperTheory.V.ZK.SCoc := by
  intro k _ _ q _ e ζ hζ v
  obtain ⟨r, lg, hr, h1, h2⟩ := ex_log q ζ hζ.eq_orderOf.symm
  have hN : ((q * r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (NeZero.pos q) hr).ne'
  choose U hU using h1
  have hs : ∀ a b, U a b = U b a := fun a b => mul_left_cancel₀ hN (by rw [← hU, ← hU, mul_comm a b]; ring)
  have hc : ∀ a b c, U b c - U (a * b) c + U a (b * c) - U a b = 0 := fun a b c =>
    mul_left_cancel₀ hN (by simp only [mul_sub, mul_add, ← hU, mul_assoc a b c]; ring)
  set u : kˣ → kˣ → ZMod q := fun a b => (U a b : ZMod q) with hu
  set w : kˣ → ZMod q := fun a => Multiplicative.toAdd (v a) with hw
  refine ⟨Finsupp.linearCombination _ (F u w _), ?_, fun x g => ?_⟩
  · rintro _ ⟨z, rfl⟩
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | single g c =>
      have := F_coc u w (fun a b c => by simp only [hu]; exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) (hc a b c))
        (fun a b => by simp [hw]) _ g
      simp only [bd, Finsupp.linearCombination_single, map_smul, map_add, map_sum, one_smul, smul_eq_mul, one_mul]
      exact mul_eq_zero_of_right _ this
  · have key : ∑ j : ZMod q, u (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd j))
        (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd 1)) = x := by
      set χ := chi q ζ hζ.pow_eq_one x with hχ
      have e1 : ((q * r : ℕ) : ℤ) * ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          q * lg (χ (Multiplicative.ofAdd 1)) := by
        simp only [Finset.mul_sum, ← hU, ← map_mul, ← ofAdd_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have := Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) fun j => lg (χ (Multiplicative.ofAdd j))
        simp only [Equiv.coe_addRight] at this
        rw [this]; simp
      obtain ⟨m, hm⟩ := h2 (x * (1 : ZMod q).val)
      have e2 : lg (χ (Multiplicative.ofAdd 1)) = r * ((x * (1 : ZMod q).val : ℕ) + q * m) := by
        have : χ (Multiplicative.ofAdd 1) = ζ ^ (x * (1 : ZMod q).val) := rfl
        rw [this]; push_cast at hm ⊢; linear_combination hm
      have e3 : ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          (x * (1 : ZMod q).val : ℕ) + q * m := mul_left_cancel₀ hN (by rw [e1, e2]; push_cast; ring)
      have := congrArg (Int.cast : ℤ → ZMod q) e3
      simpa [hu] using this
    have hp : ∀ h : Fin (2 * e + 1 + 1) → kˣ, Finsupp.linearCombination (ZMod q) (F u w _)
        (prism (ZMod q) g _ (Finsupp.single h 1)) = F u w (2 * (e + 1)) h * w g := fun h => by
      rw [← F_ins u w (fun a b => by simp only [hu, hs a b]) g (e + 1) h]
      simp only [prism, Finsupp.linearCombination_single, one_smul, map_sum, map_smul, smul_eq_mul, mul_one, one_mul,
        inv_mul_cancel_comm, ite_self]
      rfl
    simp only [zc, map_sum, cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hp, F_prod]
    rw [← Finset.sum_mul, ← key, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine congrArg (· * w g) (Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun s _ => ?_)
    have a1 : 2 * (s : ℕ) % 2 = 0 := by omega
    have a2 : ¬(2 * (s : ℕ) + 1) % 2 = 0 := by omega
    have a3 : 2 * (s : ℕ) / 2 = s := by omega
    simp only [a1, a2, a3, if_true, if_false, Fin.eta]

end
