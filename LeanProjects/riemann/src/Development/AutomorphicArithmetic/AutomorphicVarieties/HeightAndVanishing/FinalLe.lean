import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.RedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LossLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Cases
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CardLeLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SumBack

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem sum_split {ι : Type} (T : ℕ → Finset ι) (O : Finset ι) (v : ι → ℕ → ℝ) (t N q : ℕ) (L K S : ℝ)
    (hv : ∀ i e, 0 ≤ v i e) (hL : 0 ≤ L) (hK : 0 ≤ K) (hS : 0 ≤ S) (hT : ∀ e, (T e).card ≤ N) (hq : O.card ≤ q)
    (h1 : ∀ e ∈ Finset.Ico 1 t, ∀ i ∈ T e, i ∈ O ∨ v i e * L ≤ K)
    (h2 : ∀ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ S) :
    L * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, v i e ≤ L * (q * S) + t * (N * K) := by
  classical
  have step : ∀ e ∈ Finset.Ico 1 t, L * ∑ i ∈ T e, v i e ≤ L * ∑ i ∈ O, v i e + N * K := by
    intro e he
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ i ∈ T e, L * v i e ≤ ∑ i ∈ T e, ((if i ∈ O then L * v i e else 0) + K) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hO : i ∈ O
          · rw [if_pos hO]
            linarith
          · rw [if_neg hO]
            rcases h1 e he i hi with h | h
            · exact absurd h hO
            · linarith [mul_comm (v i e) L]
      _ = ∑ i ∈ T e ∩ O, L * v i e + (T e).card * K := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem]
      _ ≤ ∑ i ∈ O, L * v i e + N * K := by
          apply add_le_add
          · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => mul_nonneg hL (hv i e))
          · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT e) hK
  have hA : ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ q * S := by
    calc ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ ∑ i ∈ O, S := Finset.sum_le_sum h2
      _ = O.card * S := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ q * S := mul_le_mul_of_nonneg_right (by exact_mod_cast hq) hS
  have hB : ((Finset.Ico 1 t).card : ℝ) ≤ t := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le t 1
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  calc L * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, v i e
      = ∑ e ∈ Finset.Ico 1 t, L * ∑ i ∈ T e, v i e := Finset.mul_sum _ _ _
    _ ≤ ∑ e ∈ Finset.Ico 1 t, (L * ∑ i ∈ O, v i e + N * K) := Finset.sum_le_sum step
    _ = L * ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e + ((Finset.Ico 1 t).card : ℝ) * (N * K) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ L * (q * S) + t * (N * K) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hL) (mul_le_mul_of_nonneg_right hB hNK)

private theorem final_le (M L l q N t B : ℝ) (a b C : ℕ) (hM : M = N * t) (h3 : 3 ≤ M) (hL : L ≤ l)
    (hl : 0 ≤ l) (hlM : l ≤ M) (hq : 0 ≤ q) (hqM : q ≤ M) (hB : 0 ≤ B) (hC : a + 2 * b + 9 ≤ C) (hC' : l * q ≤ C) :
    L * (q * (B + M ^ a)) + t * (N * (M ^ 2) ^ b) + L * (N * (t * M ^ 6)) ≤ M ^ C + C * B := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hNt : N * (t * M ^ 6) = M ^ 7 := by
    rw [hM]
    ring
  have hNb : t * (N * (M ^ 2) ^ b) = M ^ (2 * b + 1) := by
    rw [hM]
    ring
  rw [hNt, hNb]
  have hX : 0 ≤ q * (B + M ^ a) := mul_nonneg hq (by positivity)
  have e1 : L * (q * (B + M ^ a)) ≤ l * (q * (B + M ^ a)) := mul_le_mul_of_nonneg_right hL hX
  have e2 : l * (q * (B + M ^ a)) = (l * q) * B + l * q * M ^ a := by ring
  have e3 : (l * q) * B ≤ C * B := mul_le_mul_of_nonneg_right hC' hB
  have hlq : l * q ≤ M * M := mul_le_mul hlM hqM hq hM0
  have e4 : l * q * M ^ a ≤ M * M * M ^ a := mul_le_mul_of_nonneg_right hlq (pow_nonneg hM0 a)
  have e4' : M * M * M ^ a = M ^ (a + 2) := by ring
  have e5 : L * M ^ 7 ≤ l * M ^ 7 := mul_le_mul_of_nonneg_right hL (pow_nonneg hM0 7)
  have e6 : l * M ^ 7 ≤ M * M ^ 7 := mul_le_mul_of_nonneg_right hlM (pow_nonneg hM0 7)
  have e6' : M * M ^ 7 = M ^ 8 := by ring
  obtain ⟨D, hD⟩ : ∃ D, C = D + 1 := ⟨C - 1, by omega⟩
  have p1 : M ^ (a + 2) ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p2 : M ^ (2 * b + 1) ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p3 : M ^ 8 ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p4 : 3 * M ^ D ≤ M * M ^ D := mul_le_mul_of_nonneg_right h3 (pow_nonneg hM0 D)
  have p5 : M ^ C = M * M ^ D := by rw [hD, pow_succ']
  linarith

theorem UpperTheory.V.HV.sumIn :
    CountII → CountV → CountVs → CountIV → SumIn := by
  unfold SumIn
  intro hII hV hVs hIV χ l j hl
  haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.instIsAlgClosure (k := ℚ))
    · rfl
    · exact Subsingleton.elim _ _
  obtain ⟨C2, hC2⟩ := hII χ
  obtain ⟨C5, hC5⟩ := hV χ
  obtain ⟨C6, hC6⟩ := hVs χ
  obtain ⟨C4, hC4⟩ := hIV χ (l : ℕ) j hl
  set Cm := max C2 (max C5 C6) with hCm
  refine ⟨C4 + 2 * Cm + 9 + (l : ℕ) * χ.N, ?_⟩
  intro h hχ t ht2 hBig B hB hLay E _ _ _ hE Ω _ _ _ ld
  classical
  haveI : NeZero h.N := ⟨h.N_pos.ne'⟩
  haveI : NeZero (Nat.totient h.N) := ⟨(Nat.totient_pos.2 h.N_pos).ne'⟩
  obtain ⟨c, hc⟩ := exists_coef (l : ℕ) (Nat.totient h.N)
  haveI := hc
  have hlp : (l : ℕ).Prime := l.2
  have hl2 : (l : ℕ) ≠ 2 := (prime_of_mem_Bchi hl).2
  have hlB : (l : ℕ) ∈ Bchi h.chi := by
    rw [hχ]
    exact hl
  have hbf := bchiFacts h t hBig
  have hlq1 : (l : ℕ) < h.q1 := (hbf.1 _ hlB).1
  have hld : (l : ℕ) < h.d := (hbf.1 _ hlB).2
  have hidx := hostIndex h
  have hNpos : 0 < h.N := h.N_pos
  have hq1N : h.q1 ≤ h.N := Nat.le_of_dvd hNpos h.host_q1_dvd_N
  have hqN : h.q ≤ h.N := Nat.le_of_dvd hNpos h.q_dvd
  have h16 : 16 ≤ h.N := Nat.le_of_dvd hNpos hidx.2.2.1
  have hlN : (l : ℕ) ≤ h.N := by omega
  set M : ℝ := (h.N : ℝ) * t with hMdef
  set L : ℝ := Real.log ((l : ℕ) : ℝ) with hLdef
  have hN1 : (1 : ℝ) ≤ h.N := by exact_mod_cast (by omega : 1 ≤ h.N)
  have hM3 : 3 ≤ M := by
    have a1 : (16 : ℝ) ≤ h.N := by exact_mod_cast h16
    have a2 : (2 : ℝ) ≤ t := by exact_mod_cast ht2
    rw [hMdef]
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hl1 : (1 : ℝ) ≤ ((l : ℕ) : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hL0 : 0 ≤ L := Real.log_nonneg hl1
  have hLl : L ≤ ((l : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((l : ℕ) : ℝ) by linarith)
    linarith
  have hNM : (h.N : ℝ) ≤ M := by
    have a2 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    rw [hMdef]
    nlinarith
  have hlM : ((l : ℕ) : ℝ) ≤ M := le_trans (by exact_mod_cast hlN) hNM
  have hqM : (h.q : ℝ) ≤ M := le_trans (by exact_mod_cast hqN) hNM
  have hKb : ∀ e, 0 < e → e < t → ∀ k ≤ Cm, (((l : ℕ) : ℝ) * h.N * e) ^ k ≤ (M ^ 2) ^ Cm := by
    intro e he0 het k hk
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have het' : (e : ℝ) ≤ t := by exact_mod_cast het.le
    have hx1 : 1 ≤ ((l : ℕ) : ℝ) * h.N * e := by
      have a1 : 1 ≤ ((l : ℕ) : ℝ) * h.N := by nlinarith
      nlinarith
    have hx2 : ((l : ℕ) : ℝ) * h.N * e ≤ M ^ 2 := by
      have a1 : (h.N : ℝ) * e ≤ M := by
        rw [hMdef]
        exact mul_le_mul_of_nonneg_left het' (by linarith)
      calc ((l : ℕ) : ℝ) * h.N * e = ((l : ℕ) : ℝ) * (h.N * e) := by ring
        _ ≤ M * M := mul_le_mul hlM a1 (by positivity) hM0
        _ = M ^ 2 := by ring
    calc (((l : ℕ) : ℝ) * h.N * e) ^ k ≤ (((l : ℕ) : ℝ) * h.N * e) ^ Cm := pow_le_pow_right₀ hx1 hk
      _ ≤ (M ^ 2) ^ Cm := pow_le_pow_left₀ (by linarith) hx2 Cm
  let Oset : Finset (DirichletCharacter c.O h.N) :=
    (Finset.Ico 1 t).biUnion (fun e => (h.X c e).filter (fun ψ => Odd (orderOf (chiP (l : ℕ) ψ))))
  have hkey : ∀ e, 0 < e → e < t → ∀ ψ ∈ h.X c e,
      Vlen (AlgebraicClosure ℚ) c e ψ ≠ ⊤ ∧
        (ψ ∈ Oset ∨ Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) * L ≤ (M ^ 2) ^ Cm) := by
    intro e he0 het ψ hψ
    have hchar := ((Host.mem_X h).1 hψ).1
    rcases (UpperTheory.V.HV.cases h t hBig c.O ψ hchar (l : ℕ) e hlp hl2 he0 het).2 hlB with hc2 | hc4 | hc5
    · have hv := hC2 h hχ t hBig (AlgebraicClosure ℚ) (l : ℕ) c e hl2 he0 het ψ hψ hc2
      exact ⟨hv.1, Or.inr (hv.2.trans (hKb e he0 het C2 (le_max_left _ _)))⟩
    · have hs := hC4 h hχ t ht2 hBig B hLay (AlgebraicClosure ℚ) c ψ hchar hc4.2.2
      refine ⟨hs.1 e he0 het, Or.inl ?_⟩
      exact Finset.mem_biUnion.2 ⟨e, Finset.mem_Ico.2 ⟨he0, het⟩, Finset.mem_filter.2 ⟨hψ, hc4.2.2⟩⟩
    · by_cases hR : h.R1 (l : ℕ) ψ ≤ 2 ^ c2 ψ
      · have hv := hC5 h hχ t hBig (AlgebraicClosure ℚ) (l : ℕ) c e hl2 he0 het ψ hψ ⟨hc5, hR⟩
        exact ⟨hv.1, Or.inr (hv.2.trans (hKb e he0 het C5 (le_trans (le_max_left _ _) (le_max_right _ _))))⟩
      · have hv := hC6 h hχ t hBig (AlgebraicClosure ℚ) (l : ℕ) c e hl2 he0 het ψ hψ ⟨hc5, not_le.1 hR⟩
        exact ⟨hv.1, Or.inr (hv.2.trans (hKb e he0 het C6 (le_trans (le_max_right _ _) (le_max_right _ _))))⟩
  have hOcard : Oset.card ≤ h.q := by
    apply (xCard c.O h.N).2 h.q (Nat.pos_of_ne_zero h.chi.ne.out) Oset
    intro ψ hψ
    obtain ⟨e, -, hψ'⟩ := Finset.mem_biUnion.1 hψ
    obtain ⟨hX, hodd⟩ := Finset.mem_filter.1 hψ'
    exact ((hostOdd h c.O ψ ((Host.mem_X h).1 hX).1).2 (l : ℕ) hlp hl2 hlq1.ne hld.ne hodd).1
  have hO2 : ∀ ψ ∈ Oset, ∑ e ∈ Finset.Ico 1 t, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) ≤ B + M ^ C4 := by
    intro ψ hψ
    obtain ⟨e, -, hψ'⟩ := Finset.mem_biUnion.1 hψ
    obtain ⟨hX, hodd⟩ := Finset.mem_filter.1 hψ'
    exact (hC4 h hχ t ht2 hBig B hLay (AlgebraicClosure ℚ) c ψ ((Host.mem_X h).1 hX).1 hodd).2
  have hXsub : ∀ e, h.X c e ⊆ h.X c 0 ∪ h.X c 1 := by
    intro e ψ hψ
    rw [Host.mem_X] at hψ
    rw [Finset.mem_union, Host.mem_X, Host.mem_X]
    have h2 := hψ.2
    unfold PsiEven at h2
    rcases Nat.even_or_odd e with he | he
    · left
      refine ⟨hψ.1, ?_⟩
      unfold PsiEven
      rw [h2, he.neg_one_pow, pow_zero]
    · right
      refine ⟨hψ.1, ?_⟩
      unfold PsiEven
      rw [h2, he.neg_one_pow, pow_one]
  have hred : ∀ e, 0 < e → e < t → plusLen (ld (l : ℕ)) e * eO (l : ℕ) c.O ≤
      ∑ ψ ∈ h.X c e, (Vlen (AlgebraicClosure ℚ) c e ψ + (lossAll (l : ℕ) h.N h.H.index e : ℕ∞) * eO (l : ℕ) c.O) := by
    intro e he0 het
    exact redAll E h.N h.H (hostLevel h E (by rw [hχ]; exact hE)) (l : ℕ) hl2 c Ω (ld (l : ℕ)) (AlgebraicClosure ℚ) e he0.ne' (h.X c e)
      (by
        ext ψ
        rw [Finset.mem_coe, Host.mem_X]
        rfl)
  have hsb := Chr.sumBack (l : ℕ) c.O (DirichletCharacter c.O h.N) (fun e => h.X c e) (h.X c 0 ∪ h.X c 1)
    (fun ψ e => Vlen (AlgebraicClosure ℚ) c e ψ) (fun e => plusLen (ld (l : ℕ)) e)
    (fun e => lossAll (l : ℕ) h.N h.H.index e) t hXsub
    (fun e he0 het => ⟨fun ψ hψ => (hkey e he0 het ψ hψ).1, hred e he0 het⟩)
  have hA : (∑ e ∈ Finset.Ico 1 t, ((plusLen (ld (l : ℕ)) e).toNat : ℝ)) ≤
      (∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X c e, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ)) +
        ((h.X c 0 ∪ h.X c 1).card : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) := hsb.2
  have hloss : ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ t * M ^ 6 := by
    calc ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, M ^ 6 := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, het⟩ := Finset.mem_Ico.1 he
          have hb := (lossLe (l : ℕ) h.N h.H.index e hlp hl2 (by omega) hidx.2.1 he1).1
          have hb' : ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ (((h.N * e) ^ 6 : ℕ) : ℝ) := by
            exact_mod_cast hb
          have het' : (e : ℝ) ≤ t := by exact_mod_cast het.le
          calc ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ (((h.N * e) ^ 6 : ℕ) : ℝ) := hb'
            _ = ((h.N : ℝ) * e) ^ 6 := by push_cast; ring
            _ ≤ M ^ 6 := by
              apply pow_le_pow_left₀ (by positivity)
              rw [hMdef]
              exact mul_le_mul_of_nonneg_left het' (by positivity)
      _ = ((Finset.Ico 1 t).card : ℝ) * M ^ 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ t * M ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Ico]
          exact_mod_cast Nat.sub_le t 1
  have hsplit : L * ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X c e, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) ≤
      L * (h.q * (B + M ^ C4)) + t * (h.N * (M ^ 2) ^ Cm) :=
    sum_split (fun e => h.X c e) Oset (fun ψ e => Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ)) t h.N h.q L
      ((M ^ 2) ^ Cm) (B + M ^ C4) (fun ψ e => Vn_nonneg (AlgebraicClosure ℚ) c e ψ) hL0 (by positivity)
      (add_nonneg hB (pow_nonneg hM0 _)) (fun e => (xCard c.O h.N).1 _) hOcard
      (fun e he ψ hψ => (hkey e (Finset.mem_Ico.1 he).1 (Finset.mem_Ico.1 he).2 ψ hψ).2) hO2
  have hT0 : ((h.X c 0 ∪ h.X c 1).card : ℝ) ≤ h.N := by exact_mod_cast (xCard c.O h.N).1 _
  have hlossnn : 0 ≤ ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have s1 := mul_le_mul_of_nonneg_left hA hL0
  rw [mul_add] at s1
  have s2 : L * (((h.X c 0 ∪ h.X c 1).card : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ)) ≤
      L * (h.N * (t * M ^ 6)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hT0 hloss hlossnn (by positivity)) hL0
  have hqC : h.q = χ.N := by
    simp only [Host.q, hχ]
  have hlqC : ((l : ℕ) : ℝ) * h.q ≤ ((C4 + 2 * Cm + 9 + (l : ℕ) * χ.N : ℕ) : ℝ) := by
    rw [hqC]
    exact_mod_cast Nat.le_add_left _ _
  have hfin := final_le M L ((l : ℕ) : ℝ) (h.q : ℝ) (h.N : ℝ) (t : ℝ) B C4 Cm (C4 + 2 * Cm + 9 + (l : ℕ) * χ.N)
    hMdef hM3 hLl (by linarith) hlM (Nat.cast_nonneg _) hqM hB (by omega) hlqC
  refine ⟨?_, ?_⟩
  · intro l' hl' e he0 het
    rw [Finset.mem_singleton] at hl'
    subst hl'
    exact hsb.1 e he0 het
  · rw [Finset.sum_singleton]
    linarith
