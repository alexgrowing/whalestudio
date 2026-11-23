import Formalism.PolynomialDimension.DigitSumValuationBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma digit_inner_one (n G t : ℕ) :
    ((univ : Finset (Fin (n+1))).filter (fun x : Fin (n+1) => ((x : ℕ) + G) % (n+1) = t % (n+1))).card = 1 := by
  set N := n + 1 with hN
  have hNpos : 0 < N := by omega
  let φ : Fin N → Fin N := fun x => ⟨((x : ℕ) + G) % N, Nat.mod_lt _ hNpos⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : ((x : ℕ) + G) % N = ((y : ℕ) + G) % N := congrArg Fin.val hxy
    have h2 : (x : ℕ) ≡ (y : ℕ) [MOD N] := Nat.ModEq.add_right_cancel' G h1
    apply Fin.ext
    rw [← Nat.mod_eq_of_lt x.isLt, ← Nat.mod_eq_of_lt y.isLt]
    exact h2
  obtain ⟨x₀, hx₀⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨t % N, Nat.mod_lt _ hNpos⟩
  rw [Finset.card_eq_one]
  refine ⟨x₀, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hx
    apply hinj
    rw [hx₀]
    exact Fin.ext hx
  · rintro rfl
    exact congrArg Fin.val hx₀

lemma digit_one_letter (P m t : ℕ) (hP : 0 < P) :
    ((univ : Finset (Fin (m+1) → Fin P)).filter (fun f => (∑ c, (f c : ℕ)) % P = t % P)).card = P ^ m := by
  rw [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (m+1) => Fin P)
    (fun p => if (∑ c, ((Fin.cons p.1 p.2 : Fin (m+1) → Fin P) c : ℕ)) % P = t % P then 1 else 0)
    (fun f => if (∑ c, (f c : ℕ)) % P = t % P then 1 else 0) (fun p => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h1 : ∀ g : Fin m → Fin P, ∑ x : Fin P,
      (if (∑ c, ((Fin.cons x g : Fin (m+1) → Fin P) c : ℕ)) % P = t % P then 1 else 0) = 1 := by
    intro g
    obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
    rw [← Finset.card_filter]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    exact digit_inner_one n _ t
  simp [h1]

theorem digit_vectors_count : DigitVectorsCount := by
  intro s m P aa hP
  have e : ((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)) =
      Fintype.piFinset (fun i => (univ : Finset (Fin (m+1) → Fin (P i))).filter
        (fun f => (∑ c, (f c : ℕ)) % P i = aa i.castSucc % P i)) := by
    ext ρ
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    rfl
  rw [e, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun i _ => digit_one_letter (P i) m (aa i.castSucc) (hP i)

theorem digitDoubleCount_of (h : DigitVectorsCount) : DigitDoubleCount := by
  intro s m P I R _ M hP
  have hswap : ∑ ρ : DigitVec s m P,
      (((Fintype.piFinset fun _ : Fin (s+1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ) =
      ∑ aa ∈ Fintype.piFinset (fun _ : Fin (s+1) => I),
        ((((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)).card : ℕ) : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_comm
  have hcount : ∀ aa : Fin (s+1) → ℕ,
      ((((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)).card : ℕ) : ℝ) =
        ((∏ i, P i ^ m : ℕ) : ℝ) := fun aa => by rw [h s m P aa hP]
  have hsplit : (∑ ρ : DigitVec s m P, ∑ q : R,
      (((Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ) * M q) =
      (∑ ρ : DigitVec s m P,
        (((Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ)) *
        ∑ q : R, M q := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [hsplit, hswap, Finset.sum_congr rfl (fun aa _ => hcount aa), Finset.sum_const,
    Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem digit_double_count : DigitDoubleCount := digitDoubleCount_of digit_vectors_count

theorem segment_bound_three_holds : DigitSumValuationBound := by
  intro p _ n r a ha hn
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1
  have hS : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
  have hreal : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = (n : ℝ) - ((p.digits n).sum : ℝ) := by
    have h1 : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) = ((n - (p.digits n).sum : ℕ) : ℝ) := by
      rw [hleg]
    rw [Nat.cast_mul, Nat.cast_sub hS, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h1
    linarith
  have hii : (n : ℝ) / ((p : ℝ) - 1) - padicValNat p n.factorial =
      ((p.digits n).sum : ℝ) / ((p : ℝ) - 1) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
    linarith
  have hY : (1 : ℝ) ≤ 8 * a + r := by
    have := (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    linarith
  have hp1' : (1 : ℝ) < p := by exact_mod_cast hp2
  refine ⟨?_, hii, ?_⟩
  · rw [hii]
    positivity
  · rw [hii, div_le_iff₀ hp1]
    rcases Nat.eq_zero_or_pos n with h0 | hnpos
    · subst h0
      have h00 : ((p.digits 0).sum : ℝ) = 0 := by simp
      rw [h00]
      unfold lgSeg
      exact mul_nonneg (by linarith [Real.logb_nonneg hp1' hY]) hp1.le
    · have hlen := Nat.digits_len p n hp2 (by omega)
      have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
        have := List.sum_le_card_nsmul (p.digits n) (p - 1)
          (fun x hx => by have := Nat.digits_lt_base hp2 hx; omega)
        simpa using this
      have hlog : (Nat.log p n : ℝ) ≤ Real.logb p (8 * a + r) := by
        have h1 : ((p : ℝ) ^ (Nat.log p n)) ≤ (n : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self p (by omega)
        calc (Nat.log p n : ℝ) ≤ Real.logb p n := by
              rw [Real.le_logb_iff_rpow_le hp1' (by exact_mod_cast hnpos), Real.rpow_natCast]
              exact h1
          _ ≤ Real.logb p (8 * a + r) :=
              Real.logb_le_logb_of_le hp1' (by exact_mod_cast hnpos) hn
      have hS' : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
        have h2 : ((p.digits n).sum : ℝ) ≤ (((p.digits n).length * (p - 1) : ℕ) : ℝ) := by
          exact_mod_cast hsum
        rw [hlen] at h2
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_add, Nat.cast_one] at h2
        linarith
      unfold lgSeg
      nlinarith [hlog, hp1]

lemma sum_update_swap {s : ℕ} (As : Fin s → Finset ℕ) (i : Fin s) (g : (Fin s → ℕ) → ℝ) :
    ∑ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, g (Function.update aa i x) =
      ((As i).card : ℝ) * ∑ aa ∈ Fintype.piFinset As, g aa := by
  have key : ∑ p ∈ Fintype.piFinset As ×ˢ As i, g (Function.update p.1 i p.2) =
      ∑ p ∈ Fintype.piFinset As ×ˢ As i, g p.1 := by
    apply Finset.sum_nbij' (fun p => (Function.update p.1 i p.2, p.1 i))
      (fun p => (Function.update p.1 i p.2, p.1 i))
    · rintro ⟨aa, x⟩ h
      simp only [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp [h.2]
      · simp [Function.update_of_ne hj, h.1 j]
    · rintro ⟨aa, x⟩ h
      simp only [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp [h.2]
      · simp [Function.update_of_ne hj, h.1 j]
    · rintro ⟨aa, x⟩ _
      simp
    · rintro ⟨aa, x⟩ _
      simp
    · rintro ⟨aa, x⟩ _
      rfl
  rw [← Finset.sum_product', key, Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem mean_share_first : MeanShareA := by
  intro s As Ap U top bad rk m X eps epsP K hAs hAp htop hbad hX hm hK hXavg hbadavg
  have hSne : (Fintype.piFinset As).Nonempty := Fintype.piFinset_nonempty.mpr hAs
  have hSc : (0 : ℝ) < (Fintype.piFinset As).card := by exact_mod_cast hSne.card_pos
  have hApc : (0 : ℝ) < Ap.card := by exact_mod_cast hAp.card_pos
  have hA : ∀ aa ∈ Fintype.piFinset As, ∑ ap ∈ Ap, bad aa ap / rk aa ap ≤
      2 * Ap.card * (∑ i ∈ U, X i aa / m aa + epsP) := by
    intro aa haa
    obtain ⟨hm0, hmrk⟩ := hm aa haa
    have hmne : m aa ≠ 0 := hm0.ne'
    have h1 : ∑ ap ∈ Ap, bad aa ap / rk aa ap ≤ ∑ ap ∈ Ap, bad aa ap * 2 / m aa := by
      refine Finset.sum_le_sum fun ap hap => ?_
      calc bad aa ap / rk aa ap ≤ bad aa ap / (m aa / 2) :=
            div_le_div_of_nonneg_left (hbad aa haa ap hap) (by positivity) (hmrk ap hap)
        _ = bad aa ap * 2 / m aa := by rw [div_div_eq_mul_div]
    have h2 := hbadavg aa haa
    rw [div_le_iff₀ hApc] at h2
    calc ∑ ap ∈ Ap, bad aa ap / rk aa ap ≤ ∑ ap ∈ Ap, bad aa ap * 2 / m aa := h1
      _ = (∑ ap ∈ Ap, bad aa ap) * 2 / m aa := by rw [← Finset.sum_div, ← Finset.sum_mul]
      _ ≤ ((∑ i ∈ U, X i aa + epsP * m aa) * Ap.card) * 2 / m aa :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by norm_num)) hm0.le
      _ = 2 * Ap.card * (∑ i ∈ U, X i aa / m aa + epsP) := by
          rw [← Finset.sum_div]
          field_simp
  have hB : ∀ i ∈ U, ∑ aa ∈ Fintype.piFinset As, X i aa / m aa ≤
      (Fintype.piFinset As).card * K * eps i := by
    intro i hi
    have hAsc : (0 : ℝ) < (As i).card := by exact_mod_cast (hAs i).card_pos
    have hupd : ∀ aa ∈ Fintype.piFinset As, ∀ x ∈ As i, Function.update aa i x ∈ Fintype.piFinset As := by
      intro aa haa x hx
      rw [Fintype.mem_piFinset] at haa ⊢
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simpa using hx
      · rw [Function.update_of_ne hj]
        exact haa j
    have hinner : ∀ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, X i (Function.update aa i x) /
        m (Function.update aa i x) ≤ K * (As i).card * eps i := by
      intro aa haa
      have hT := (hm _ (hupd aa haa _ (htop i hi))).1
      have hTne : m (Function.update aa i (top i)) ≠ 0 := hT.ne'
      have hK0 : 0 ≤ K := by
        have hh := hK i hi _ (hupd aa haa _ (htop i hi))
        rw [Function.update_idem] at hh
        nlinarith
      have hle : ∀ x ∈ As i, X i (Function.update aa i x) / m (Function.update aa i x) ≤
          X i (Function.update aa i x) * K / m (Function.update aa i (top i)) := by
        intro x hx
        have hmx := (hm _ (hupd aa haa x hx)).1
        have hKx := hK i hi _ (hupd aa haa x hx)
        rw [Function.update_idem] at hKx
        rw [div_le_div_iff₀ hmx hT]
        have hXx := hX i hi _ (hupd aa haa x hx)
        nlinarith [mul_le_mul_of_nonneg_left hKx hXx]
      have havg := hXavg i hi aa haa
      rw [div_le_iff₀ hAsc] at havg
      calc ∑ x ∈ As i, X i (Function.update aa i x) / m (Function.update aa i x)
          ≤ ∑ x ∈ As i, X i (Function.update aa i x) * K / m (Function.update aa i (top i)) :=
            Finset.sum_le_sum hle
        _ = (∑ x ∈ As i, X i (Function.update aa i x)) * K / m (Function.update aa i (top i)) := by
            rw [← Finset.sum_div, ← Finset.sum_mul]
        _ ≤ (eps i * m (Function.update aa i (top i)) * (As i).card) * K /
              m (Function.update aa i (top i)) := by
            apply div_le_div_of_nonneg_right _ hT.le
            exact mul_le_mul_of_nonneg_right havg hK0
        _ = K * (As i).card * eps i := by
            field_simp
    have hswap := sum_update_swap As i (fun aa => X i aa / m aa)
    beta_reduce at hswap
    have htot : ((As i).card : ℝ) * ∑ aa ∈ Fintype.piFinset As, X i aa / m aa ≤
        ((As i).card : ℝ) * ((Fintype.piFinset As).card * K * eps i) := by
      rw [← hswap]
      calc ∑ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, X i (Function.update aa i x) / m (Function.update aa i x)
          ≤ ∑ aa ∈ Fintype.piFinset As, K * (As i).card * eps i := Finset.sum_le_sum hinner
        _ = ((As i).card : ℝ) * ((Fintype.piFinset As).card * K * eps i) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    exact le_of_mul_le_mul_left htot hAsc
  rw [div_le_iff₀ (by positivity)]
  calc ∑ aa ∈ Fintype.piFinset As, ∑ ap ∈ Ap, bad aa ap / rk aa ap
      ≤ ∑ aa ∈ Fintype.piFinset As, 2 * Ap.card * (∑ i ∈ U, X i aa / m aa + epsP) := Finset.sum_le_sum hA
    _ = 2 * Ap.card * (∑ i ∈ U, ∑ aa ∈ Fintype.piFinset As, X i aa / m aa +
          (Fintype.piFinset As).card * epsP) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Ap.card * (∑ i ∈ U, (Fintype.piFinset As).card * K * eps i +
          (Fintype.piFinset As).card * epsP) := by
        gcongr with i hi
        exact hB i hi
    _ = (2 * K * (∑ i ∈ U, eps i) + 2 * epsP) * ((Fintype.piFinset As).card * Ap.card) := by
        rw [← Finset.mul_sum]
        ring

lemma mean_share_abs {α β R : Type} [Fintype β] [Fintype R] (W : Finset α) (compat : β → α → Prop)
    [∀ ρ aa, Decidable (compat ρ aa)] (ny : ℕ) (hny : 0 < ny)
    (hcount : ∀ aa ∈ W, ((univ : Finset β).filter (fun ρ => compat ρ aa)).card = ny)
    (bad rk : β → R → α → ℝ) (Mlo Mhi : R → ℝ) (eps K : ℝ) (hW : W.Nonempty) (heps : 0 ≤ eps) (hK : 0 ≤ K)
    (hbad : ∀ ρ q aa, 0 ≤ bad ρ q aa) (hMlo : ∀ q, 0 ≤ Mlo q) (hMhi : ∀ q, Mhi q ≤ K * Mlo q)
    (hrk : ∀ ρ q, ∀ aa ∈ W, compat ρ aa → Mlo q / 2 ≤ rk ρ q aa)
    (hsum : ∀ ρ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa ≤
      eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * Mhi q) :
    (∑ aa ∈ W, (∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, bad ρ q aa) /
      (∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, rk ρ q aa)) / (W.card : ℝ) ≤ 2 * K * eps := by
  classical
  have hM0 : 0 ≤ ∑ q, Mlo q := Finset.sum_nonneg fun q _ => hMlo q
  have hWc : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hnyR : (0 : ℝ) < ny := by exact_mod_cast hny
  set N : α → ℝ := fun aa => ∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, bad ρ q aa with hN
  set D : α → ℝ := fun aa => ∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, rk ρ q aa with hD
  show (∑ aa ∈ W, N aa / D aa) / (W.card : ℝ) ≤ 2 * K * eps
  have hN0 : ∀ aa, 0 ≤ N aa := fun aa =>
    Finset.sum_nonneg fun ρ _ => Finset.sum_nonneg fun q _ => hbad ρ q aa
  have hDlow : ∀ aa ∈ W, (ny : ℝ) * (∑ q, Mlo q) / 2 ≤ D aa := by
    intro aa haa
    calc (ny : ℝ) * (∑ q, Mlo q) / 2 = ∑ ρ ∈ univ.filter (fun ρ : β => compat ρ aa), ∑ q, Mlo q / 2 := by
          rw [Finset.sum_const, hcount aa haa, nsmul_eq_mul, ← Finset.sum_div]
          ring
      _ ≤ D aa := Finset.sum_le_sum fun ρ hρ => Finset.sum_le_sum fun q _ =>
          hrk ρ q aa haa (Finset.mem_filter.mp hρ).2
  have hcard : ∑ ρ : β, ((W.filter (fun aa => compat ρ aa)).card : ℝ) = (W.card : ℝ) * ny := by
    have e : ∑ ρ : β, ((W.filter (fun aa => compat ρ aa)).card : ℝ) =
        ∑ aa ∈ W, (((univ : Finset β).filter (fun ρ => compat ρ aa)).card : ℝ) := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_comm' (t' := W) (s' := fun aa => (univ : Finset β).filter fun ρ => compat ρ aa)
        (fun ρ aa => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)
    rw [e, Finset.sum_congr rfl (fun aa haa => by rw [hcount aa haa]), Finset.sum_const, nsmul_eq_mul]
  have hNsum : ∑ aa ∈ W, N aa ≤ eps * K * (∑ q, Mlo q) * ((W.card : ℝ) * ny) := by
    have hsw : ∑ aa ∈ W, N aa =
        ∑ ρ : β, ∑ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa := by
      simp only [hN]
      rw [Finset.sum_comm' (t' := univ) (s' := fun ρ => W.filter fun aa => compat ρ aa)
        (fun aa ρ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)]
      exact Finset.sum_congr rfl fun ρ _ => Finset.sum_comm
    rw [hsw, ← hcard, Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ _ => ?_
    calc ∑ q, ∑ aa ∈ W.filter (fun aa => compat ρ aa), bad ρ q aa
        ≤ ∑ q, eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * Mhi q :=
          Finset.sum_le_sum fun q _ => hsum ρ q
      _ ≤ ∑ q, eps * ((W.filter (fun aa => compat ρ aa)).card : ℝ) * (K * Mlo q) :=
          Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hMhi q) (by positivity)
      _ = eps * K * (∑ q, Mlo q) * ((W.filter (fun aa => compat ρ aa)).card : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => by ring
  rcases hM0.lt_or_eq with hMpos | hMz
  · have hMne : (∑ q, Mlo q) ≠ 0 := hMpos.ne'
    have hnyne : (ny : ℝ) ≠ 0 := hnyR.ne'
    have hper : ∀ aa ∈ W, N aa / D aa ≤ N aa * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by
      intro aa haa
      have hpos : 0 < (ny : ℝ) * (∑ q, Mlo q) / 2 := by positivity
      calc N aa / D aa ≤ N aa / ((ny : ℝ) * (∑ q, Mlo q) / 2) :=
            div_le_div_of_nonneg_left (hN0 aa) hpos (hDlow aa haa)
        _ = N aa * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by rw [div_div_eq_mul_div]
    rw [div_le_iff₀ hWc]
    calc ∑ aa ∈ W, N aa / D aa ≤ ∑ aa ∈ W, N aa * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := Finset.sum_le_sum hper
      _ = (∑ aa ∈ W, N aa) * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
      _ ≤ (eps * K * (∑ q, Mlo q) * ((W.card : ℝ) * ny)) * 2 / ((ny : ℝ) * (∑ q, Mlo q)) := by
          gcongr
      _ = 2 * K * eps * W.card := by
          field_simp
  · have hsum0 : ∑ aa ∈ W, N aa = 0 := by
      apply le_antisymm
      · calc ∑ aa ∈ W, N aa ≤ eps * K * (∑ q, Mlo q) * ((W.card : ℝ) * ny) := hNsum
          _ = 0 := by rw [← hMz]; ring
      · exact Finset.sum_nonneg fun aa _ => hN0 aa
    have hz : ∀ aa ∈ W, N aa = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun aa _ => hN0 aa).mp hsum0
    rw [Finset.sum_congr rfl (fun aa haa => by rw [hz aa haa, zero_div]), Finset.sum_const_zero, zero_div]
    positivity

theorem meanShareB_of (h : DigitVectorsCount) : MeanShareB := by
  intro s m P I R _ bad rk Mlo Mhi eps K hP hI heps hK hbad hMlo hMhi hrk hsum
  classical
  convert mean_share_abs (Fintype.piFinset fun _ : Fin (s+1) => I) DigitCompat (∏ i, P i ^ m)
    (Finset.prod_pos fun i _ => pow_pos (hP i) m)
    (fun aa _ => by convert h s m P aa hP) bad rk Mlo Mhi eps K
    (Fintype.piFinset_nonempty.mpr fun _ => hI) heps hK hbad hMlo hMhi hrk (by convert hsum)

theorem mean_share_second : MeanShareB := meanShareB_of digit_vectors_count

theorem segment_share_sum : SegShareSum := by
  have he2 : (1 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨fun t Y epsP eps hY heps hP => ?_, fun Jn N N₁ Y t κ hY hN₁ hN hκ1 hκ => ?_⟩
  · have hY0 : 0 < Y := by linarith
    have hS : ∑ i, eps i ≤ (t : ℝ) * (28 / Y) := by
      calc ∑ i, eps i ≤ ∑ _i : Fin t, 28 / Y := Finset.sum_le_sum fun i _ => heps i
        _ = (t : ℝ) * (28 / Y) := by simp
    have hexp : Real.exp (2 / Y) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by
      rw [div_le_iff₀ hY0]
      linarith)
    have hexp0 : 0 < Real.exp (2 / Y) := Real.exp_pos _
    have h28 : 0 ≤ (t : ℝ) * (28 / Y) := by positivity
    have key : Real.exp (2 / Y) * (∑ i, eps i) ≤ Real.exp 2 * ((t : ℝ) * (28 / Y)) := by
      rcases le_or_gt (∑ i, eps i) 0 with hneg | hpos
      · nlinarith [hexp0, hneg, h28, Real.exp_pos 2]
      · calc Real.exp (2 / Y) * (∑ i, eps i) ≤ Real.exp 2 * (∑ i, eps i) :=
            mul_le_mul_of_nonneg_right hexp hpos.le
          _ ≤ Real.exp 2 * ((t : ℝ) * (28 / Y)) := mul_le_mul_of_nonneg_left hS (Real.exp_pos 2).le
    have h5 : (5 : ℝ) / Y ≤ 28 / Y := div_le_div_of_nonneg_right (by norm_num) hY0.le
    have h28' : 28 / Y ≤ Real.exp 2 * (28 / Y) := le_mul_of_one_le_left (by positivity) he2
    constructor
    · have e1 : 2 * Real.exp 2 * ((t : ℝ) + 1) * 28 / Y =
          2 * (Real.exp 2 * ((t : ℝ) * (28 / Y))) + 2 * (Real.exp 2 * (28 / Y)) := by ring
      rw [e1]
      linarith
    · have e1 : 2 * Real.exp 2 * 28 * ((t : ℝ) + 1) / Y =
          2 * Real.exp 2 * ((t : ℝ) * (28 / Y) + 28 / Y) := by ring
      rw [e1]
      have hsum' : (∑ i, eps i) + epsP ≤ (t : ℝ) * (28 / Y) + 28 / Y := by linarith
      have h2e : 0 < 2 * Real.exp 2 := by positivity
      exact mul_le_mul_of_nonneg_left hsum' h2e.le
  · have hY0 : 0 < Y := by linarith
    have hN₁R : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
    have hper : ∀ j, κ j ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y := by
      intro j
      have htj : (0 : ℝ) ≤ t j := Nat.cast_nonneg _
      by_cases hc : (N₁ : ℝ) ≤ Y
      · have h1 := hκ hc j
        have h2 : 2 * Real.exp 2 * 28 * ((t j : ℝ) + 1) / Y ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y := by
          apply div_le_div_of_nonneg_right _ hY0.le
          nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos 2).le (by linarith : (0:ℝ) ≤ t j + 1))
            (by linarith : (0:ℝ) ≤ N₁ - 1)]
        linarith
      · push_neg at hc
        have hX : (1 : ℝ) ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) := by nlinarith [he2, htj]
        have h1 : (1 : ℝ) ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y := by
          rw [le_div_iff₀ hY0]
          nlinarith [hX, hN₁R, hc]
        linarith [hκ1 j]
    refine ⟨hper, ?_⟩
    calc ∑ j, κ j ≤ ∑ j, 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y :=
          Finset.sum_le_sum fun j _ => hper j
      _ = 56 * Real.exp 2 * N₁ / Y * ∑ j, ((t j : ℝ) + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 56 * Real.exp 2 * N₁ / Y * N := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hN
      _ = 56 * Real.exp 2 * N * N₁ / Y := by ring

theorem change_lattice_good_rank : ChangeLatticeGoodRank := by
  intro O _ _ _ π _ L L' _ _ _ _ _ _ _ _ f f' φ c y n D hc hφ hgood
  obtain ⟨u, v, huv⟩ := hgood
  obtain ⟨k₀, hk₀⟩ := hc
  refine ⟨φ ∘ₗ u, (k₀ * k₀) • (v ∘ₗ φ.dualMap), ?_⟩
  have hdual : ∀ x, φ.dualMap (f' (φ (u x))) = (c * c) • f (u x) := by
    intro x
    refine LinearMap.ext fun z => ?_
    simp [LinearMap.dualMap_apply, hφ]
  apply LinearMap.ext
  intro x
  have h1 := LinearMap.congr_fun huv x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  rw [hdual, map_smul, h1, smul_smul, smul_smul]
  congr 1
  have e : π ^ (D + 2 * y) = π ^ D * π ^ y * π ^ y := by ring
  rw [e, hk₀]
  ring

theorem direct_sum_partners : DirectSumPartners := by
  intro O _ _ _ π _ M A B _ _ _ _ b n g D hsat hprim
  constructor
  · intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨z, hz⟩ := hx
    have hd : ∀ d, x d ∈ LinearMap.range (g d) := by
      intro d
      apply hsat d
      rw [LinearMap.mem_range]
      refine ⟨z d, ?_⟩
      have := congrFun hz d
      simpa using this
    choose w hw using fun d => LinearMap.mem_range.mp (hd d)
    rw [LinearMap.mem_range]
    refine ⟨w, funext fun d => ?_⟩
    simpa using hw d
  · rintro x ⟨d₀, i, hi⟩
    obtain ⟨u₀, hu₀⟩ := hprim d₀ (x d₀) ⟨i, hi⟩
    refine ⟨Pi.single d₀ u₀, ?_⟩
    rw [Finset.sum_eq_single d₀]
    · simpa using hu₀
    · intro d _ hd
      rw [Pi.single_eq_of_ne hd, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem direct_sum_good_rank : DirectSumGoodRank := by
  intro O _ _ _ π _ M A B _ _ _ _ _ _ _ _ f n D hf
  choose u v huv using hf
  let e : (Σ d : Fin M, Fin (n d)) ≃ Fin (∑ d, n d) := finSigmaFinEquiv
  refine ⟨LinearMap.pi (fun d => u d ∘ₗ LinearMap.funLeft O O (fun j => e ⟨d, j⟩)),
    LinearMap.pi (fun k => LinearMap.proj (e.symm k).2 ∘ₗ v (e.symm k).1 ∘ₗ
      LinearMap.proj (e.symm k).1), ?_⟩
  apply LinearMap.ext
  intro x
  funext k
  have h2 := congrFun (LinearMap.congr_fun (huv (e.symm k).1) (fun j => x (e ⟨(e.symm k).1, j⟩)))
    (e.symm k).2
  exact h2.trans (by simp)

theorem det_leading_diagonal : DetLeadDiag := by
  intro K _ n J A d hdeg hcoeff
  have hprod : ∀ σ : Equiv.Perm (Fin n), (∏ i, A (σ i) i).coeff (n * J) = ∏ i, (A (σ i) i).coeff J := by
    intro σ
    have h1 := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => A (σ i) i) J
      (fun i _ => hdeg (σ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  rw [Matrix.det_apply']
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_intCast, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : Fin n, J := Finset.sum_le_sum fun i _ => hdeg (σ i) i
      _ = n * J := by simp
  · rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single 1]
    · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [hcoeff]; simp
    · intro σ _ hσ
      rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.ext hσ)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hcoeff, if_neg (by simpa using hi)]), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem mat_comm_scalar {O : Type} [CommRing O] [IsDomain O] {m : ℕ} (X Y : Matrix (Fin m) (Fin m) O) (c : O)
    (hc : c ≠ 0) (h : X * Y = c • (1 : Matrix (Fin m) (Fin m) O)) : Y * X = c • (1 : Matrix (Fin m) (Fin m) O) := by
  have hdet : X.det * Y.det = c ^ m := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hX : X.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero m hc hdet.symm
  have h2 : X * (Y * X - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, sub_self]
  have h3 : X.det • (Y * X - c • 1) = 0 := by
    calc X.det • (Y * X - c • 1) = (X.adjugate * X) * (Y * X - c • 1) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = X.adjugate * (X * (Y * X - c • 1)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [h2, Matrix.mul_zero]
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  rw [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, mul_eq_zero] at h4
  have h5 := h4.resolve_left hX
  rw [Matrix.sub_apply, sub_eq_zero] at h5
  exact h5

theorem partner_converse : PartnerConverse := by
  intro O _ _ _ π hπ A B _ _ _ _ _ _ _ _ b n D hg
  obtain ⟨u, v, huv⟩ := hg
  have huv' : ∀ x, v (b (u x)) = π ^ D • x := by
    intro x
    have := congrArg (fun T => T x) huv
    simpa using this
  have hπD : π ^ D ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hinj : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := huv' x
    rw [hx, map_zero, map_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hπD
  obtain ⟨m, S⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O A) (LinearMap.range u)
  have hm : m = n := by
    have h1 : Module.finrank O (LinearMap.range u) = m := by
      rw [Module.finrank_eq_card_basis S.bN]; simp
    rw [← h1, ← (LinearEquiv.finrank_eq (LinearEquiv.ofInjective u hinj))]
    simp
  subst hm
  let g : (Fin m → O) →ₗ[O] A := (Pi.basisFun O (Fin m)).constr O (fun i => S.bM (S.f i))
  let P : A →ₗ[O] (Fin m → O) := LinearMap.pi fun i => S.bM.coord (S.f i)
  have hg_apply : ∀ z, g z = ∑ i, z i • S.bM (S.f i) := by
    intro z
    simp [g, Module.Basis.constr_apply_fintype]
  have hrepr_f : ∀ z i, S.bM.repr (g z) (S.f i) = z i := by
    intro z i
    rw [hg_apply, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : S.f j ≠ S.f i := fun e => hj (S.f.injective e)
      simp [Finsupp.single_eq_of_ne (Ne.symm this)]
    · simp
  have hrepr_nf : ∀ z j, j ∉ Set.range S.f → S.bM.repr (g z) j = 0 := by
    intro z j hj
    rw [hg_apply, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have : S.f i ≠ j := fun e => hj ⟨i, e⟩
    simp [Finsupp.single_eq_of_ne (Ne.symm this)]
  have hPg : ∀ z, P (g z) = z := by
    intro z; funext i
    simp [P, hrepr_f]
  have hgP : ∀ y : A, (∀ j, j ∉ Set.range S.f → S.bM.repr y j = 0) → g (P y) = y := by
    intro y hy
    apply S.bM.ext_elem
    intro j
    by_cases hj : j ∈ Set.range S.f
    · obtain ⟨i, rfl⟩ := hj
      rw [hrepr_f]; simp [P]
    · rw [hrepr_nf _ _ hj, hy j hj]
  have hu_nf : ∀ x j, j ∉ Set.range S.f → S.bM.repr (u x) j = 0 := by
    intro x j hj
    exact S.repr_eq_zero_of_notMem_range ⟨u x, LinearMap.mem_range_self u x⟩ hj
  let T : (Fin m → O) →ₗ[O] (Fin m → O) := P ∘ₗ u
  let W : (Fin m → O) →ₗ[O] (Fin m → O) := v ∘ₗ b ∘ₗ g
  have hgT : ∀ x, g (T x) = u x := fun x => hgP (u x) (hu_nf x)
  have hWT : W ∘ₗ T = π ^ D • LinearMap.id := by
    apply LinearMap.ext; intro x
    simp only [W, LinearMap.comp_apply]
    rw [hgT x, huv' x]; simp
  have hTW : ∀ x, T (W x) = π ^ D • x := by
    have h1 : LinearMap.toMatrix' W * LinearMap.toMatrix' T = π ^ D • (1 : Matrix (Fin m) (Fin m) O) := by
      rw [← LinearMap.toMatrix'_comp, hWT]; simp
    have h2 := mat_comm_scalar _ _ _ hπD h1
    rw [← LinearMap.toMatrix'_comp] at h2
    have h3 : T ∘ₗ W = π ^ D • LinearMap.id := by
      apply LinearMap.toMatrix'.injective
      rw [h2]; simp
    intro x
    have := congrArg (fun Z => Z x) h3
    simpa using this
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z z' h
    rw [← hPg z, ← hPg z', h]
  · rintro x ⟨z, hz⟩
    refine ⟨P x, hgP x ?_⟩
    intro j hj
    have := hrepr_nf z j hj
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hπ.ne_zero
  · rintro x ⟨i, hi⟩
    by_contra hall
    push Not at hall
    choose c hc using fun j => hall (Module.Free.chooseBasis O B j)
    let lam : Module.Dual O B := (Module.Free.chooseBasis O B).constr O c
    have hb : b (g x) = π ^ (D + 1) • lam := by
      apply (Module.Free.chooseBasis O B).ext
      intro j
      simp [lam, hc j]
    have h1 : W x = π ^ (D + 1) • v lam := by
      simp only [W, LinearMap.comp_apply, hb, map_smul]
    have h2 := hTW x
    rw [h1, map_smul, pow_succ, mul_smul] at h2
    have h3 : π • T (v lam) = x := smul_right_injective _ hπD h2
    apply hi
    rw [← h3]
    exact ⟨T (v lam) i, by simp⟩

end Formalism.CountingSumsFrames
