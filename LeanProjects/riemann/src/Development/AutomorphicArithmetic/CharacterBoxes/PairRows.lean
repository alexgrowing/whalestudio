import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
import Development.AutomorphicArithmetic.CharacterBoxes.EventuallyRankLeRpowOfLtOneDivFiftytwo
import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
import Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

private theorem boxes_step (f q i : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f) (hξ : ξ.IsPrimitive)
    (hq : q.Prime) (h2 : q ≠ 2) (hf : ¬ q ∣ f) (hi : i ≤ 1) :
    ∃ (M : ℕ) (ψ : DirichletCharacter ℂ M), M = f * q ^ i ∧ ψ.IsPrimitive ∧
      ∀ n : ℕ, ψ (n : ZMod M) = ξ (n : ZMod f) * QH.J q n ^ i := by
  interval_cases i
  · exact ⟨f, ξ, by simp, hξ, fun n => by simp⟩
  · obtain ⟨ψ, hψ, -, hn⟩ := QH.twist_prim f q ξ hξ hq h2 hf
    exact ⟨f * q, ψ, by simp, hψ, fun n => by simp [hn]⟩

private theorem boxes_core {M : ℕ} {eps Y X : ℝ} {q d : ℕ} (hM : 0 < M) (h : PairGood M eps Y X q d)
    (ρ : Formalism.HC.PChar) (hρ : ρ.IsReal) (h8 : ρ.N ∣ 8) (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (f : ℕ → ℂ)
    (hf : ∀ a : ℕ, a % 2 = 1 → f a = tw ρ.val q d i j a) (Q : ℝ)
    (hQ : Q = 8 * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps ^ (j : ℕ)) : GoodAllFor Q f (8 * q * d) := by
  intro N _ χ hind
  obtain ⟨hprim, hval⟩ := hind
  have hi : (i : ℕ) ≤ 1 := by have := i.isLt; omega
  have hj : (j : ℕ) ≤ 1 := by have := j.isLt; omega
  have hw := h.pair
  have hq := hw.q_prime
  have hd := hw.d_prime
  have hqm := hw.q_mod
  have hdm := hw.d_mod
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  haveI := ρ.ne
  have h8' : ρ.N ∣ 2 ^ 3 := h8
  have hqN : ¬ q ∣ ρ.N := fun hqn =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow (dvd_trans hqn h8')))
  obtain ⟨M1, ψ1, hM1, hψ1, hv1⟩ := boxes_step ρ.N q i ρ.χ ρ.prim hq hq2 hqN hi
  haveI : NeZero M1 := ⟨by rw [hM1]; exact mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hq.ne_zero)⟩
  have hdM1 : ¬ d ∣ M1 := by
    rw [hM1]
    intro hdd
    rcases (Nat.Prime.dvd_mul hd).mp hdd with h1 | h1
    · exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow (dvd_trans h1 h8')))
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).mp (hd.dvd_of_dvd_pow h1)).symm
  obtain ⟨M2, ψ, hM2, hψ, hv2⟩ := boxes_step M1 d j ψ1 hψ1 hd hd2 hdM1 hj
  haveI : NeZero M2 := ⟨by rw [hM2]; exact mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hd.ne_zero)⟩
  have hψv : ∀ n : ℕ, ψ n = tw ρ.val q d i j n := by
    intro n
    rw [hv2, hv1]
    simp only [tw, PChar.val, QH.J]
  have hodd : ∀ a : ℕ, a.Coprime 2 → a % 2 = 1 := by
    intro a ha
    rcases Nat.even_or_odd a with ⟨k, hk⟩ | ho
    · exfalso
      have h2g : 2 ∣ Nat.gcd a 2 := Nat.dvd_gcd ⟨k, by omega⟩ dvd_rfl
      rw [ha] at h2g
      omega
    · exact Nat.odd_iff.mp ho
  have hagree : ∀ n : ℕ, n.Coprime (8 * q * d) → χ n = ψ n := by
    intro n hn
    have h2 : n.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨4 * q * d, by ring⟩ hn
    rw [hval n hn, hf n (hodd n h2), hψv]
  have h8qd : 8 * q * d ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hq.ne_zero) hd.ne_zero
  have huniq := QH.ind_unique N M2 (8 * q * d) χ ψ h8qd hprim hψ hagree
  obtain ⟨hNM, hh⟩ := Sigma.mk.inj_iff.mp huniq
  subst hNM
  have e : χ = ψ := eq_of_heq hh
  have hχv : ∀ n : ℕ, χ n = tw ρ.val q d i j n := fun n => by rw [e]; exact hψv n
  have hqX : (q : ℝ) ≤ GlobalTheoryTheory.X1 Y eps := by
    unfold GlobalTheoryTheory.X1
    calc (q : ℝ) = Real.exp (Real.log q) := (Real.exp_log (by exact_mod_cast hq.pos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hw.q_up
  have hdX : (d : ℝ) ≤ GlobalTheoryTheory.X2 Y eps := by
    unfold GlobalTheoryTheory.X2
    calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log (by exact_mod_cast hd.pos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hw.d_up
  have hX1 : 0 ≤ GlobalTheoryTheory.X1 Y eps := by unfold GlobalTheoryTheory.X1; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  unfold GlobalTheoryTheory.GoodFor
  refine ⟨hprim, fun a => ?_, ?_, ?_⟩
  · rw [← ZMod.natCast_zmod_val a, hχv]
    generalize a.val = n
    have hr : (ρ.χ (n : ZMod ρ.N)).im = 0 := hρ _
    have e1 : (((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ (i : ℕ)).im = 0 := by
      rw [← Int.cast_pow]; exact Complex.intCast_im _
    have e2 : (((jacobiSym (n : ℤ) d : ℤ) : ℂ) ^ (j : ℕ)).im = 0 := by
      rw [← Int.cast_pow]; exact Complex.intCast_im _
    simp only [tw, PChar.val]
    rw [Complex.mul_im, Complex.mul_im, hr, e1, e2]
    ring
  · rw [hQ, hM2, hM1]
    push_cast
    have hNr : (ρ.N : ℝ) ≤ 8 := by exact_mod_cast Nat.le_of_dvd (by norm_num) h8
    have hqi : (q : ℝ) ^ (i : ℕ) ≤ GlobalTheoryTheory.X1 Y eps := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h0 | h1
      · rw [h0, pow_zero]; linarith
      · rw [h1, pow_one]; exact hqX
    have hdj : (d : ℝ) ^ (j : ℕ) ≤ GlobalTheoryTheory.X2 Y eps ^ (j : ℕ) := pow_le_pow_left₀ (by positivity) hdX _
    exact mul_le_mul (mul_le_mul hNr hqi (by positivity) (by norm_num)) hdj (by positivity)
      (mul_nonneg (by norm_num) hX1)
  · intro s hs hsQ
    have hind' : An.Induces χ (tw ρ.val q d i j) (2 * M * q * d) := by
      unfold An.Induces
      refine ⟨hprim, fun a ha => ?_⟩
      have h2 : a.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨M * q * d, by ring⟩ ha
      have hqa : a.Coprime q := Nat.Coprime.coprime_dvd_right ⟨2 * M * d, by ring⟩ ha
      have hda : a.Coprime d := Nat.Coprime.coprime_dvd_right ⟨2 * M * q, by ring⟩ ha
      have h8a : a.Coprime (8 * q * d) := by
        have e8 : (8 : ℕ) = 2 ^ 3 := by norm_num
        rw [e8]
        exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 h2) hqa) hda
      rw [hval a h8a, hf a (hodd a h2)]
    have hbox := h.boxes ρ hρ (dvd_mul_of_dvd_left h8 M) i j hij _ χ hind'
    apply hbox s hs
    refine le_trans hsQ ?_
    rw [hQ]
    unfold height GlobalTheoryTheory.X1 GlobalTheoryTheory.X2
    have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hpos : 0 ≤ 8 * Real.exp (Y ^ (eps / 5)) * Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) ^ (j : ℕ) := by
      positivity
    nlinarith

private theorem boxes_kron_odd (D : ℤ) (a : ℕ) (ha : a % 2 = 1) : GlobalTheoryTheory.kronSym D a = jacobiSym D a := by
  have h2 : ¬ 2 ∣ a := by omega
  simp [GlobalTheoryTheory.kronSym, Nat.factorization_eq_zero_of_not_dvd h2]

private theorem boxes_kron_neg (q a : ℕ) (hq : q % 4 = 3) (ha : a % 2 = 1) :
    GlobalTheoryTheory.kron (-(q : ℤ)) a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) := by
  have hao : Odd a := Nat.odd_iff.mpr ha
  have key : jacobiSym (-(q : ℤ)) a = jacobiSym (a : ℤ) q := by
    rw [jacobiSym.neg _ hao, ← jacobiSym.quadratic_reciprocity_if ha (by omega : q % 2 = 1)]
    rcases Nat.odd_mod_four_iff.mp ha with h1 | h3
    · simp [h1, ZMod.χ₄_nat_one_mod_four h1]
    · simp [h3, hq, ZMod.χ₄_nat_three_mod_four h3]
  simp only [GlobalTheoryTheory.kron]
  rw [boxes_kron_odd _ _ ha, key]

open DirichletCharacter in
private theorem real_character_mod_eight : ∃ ρ : Formalism.HC.PChar, ρ.IsReal ∧ ρ.N ∣ 8 ∧
    ∀ a : ℕ, a % 2 = 1 → GlobalTheoryTheory.chi8 a = ρ.val a := by
  obtain ⟨χ, hχ⟩ : ∃ χ : DirichletCharacter ℂ 8, ∀ a : ZMod 8, χ a = ((ZMod.χ₈ a : ℤ) : ℂ) :=
    ⟨ZMod.χ₈.ringHomComp (Int.castRingHom ℂ), fun a => by simp⟩
  have hprim : χ.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    have hd := DirichletCharacter.conductor_dvd_level χ
    have hc0 := DirichletCharacter.conductor_ne_zero χ
    by_contra hne
    have h4 : DirichletCharacter.conductor χ ∣ 4 := by
      have hle : DirichletCharacter.conductor χ ≤ 8 := Nat.le_of_dvd (by norm_num) hd
      interval_cases h : DirichletCharacter.conductor χ <;> omega
    obtain ⟨h4', χ₀, e⟩ := DirichletCharacter.FactorsThrough.mono
      (hχ := DirichletCharacter.factorsThrough_conductor χ) (hd := h4) (hm := (by norm_num : 4 ∣ 8))
    have h5 := DFunLike.congr_fun e ((5 : ℤ) : ZMod 8)
    have hcop : IsCoprime (5 : ℤ) ((8 : ℕ) : ℤ) := ⟨-3, 2, by norm_num⟩
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ h4' hcop] at h5
    have e1 : ((5 : ℤ) : ZMod 4) = 1 := by decide
    have e2 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
    rw [e1, map_one, hχ, e2] at h5
    norm_num at h5
  refine ⟨⟨8, χ, hprim⟩, fun a => ?_, dvd_refl 8, fun a ha => ?_⟩
  · show (χ a).im = 0
    rw [hχ]
    simp
  · show GlobalTheoryTheory.kron 2 a = χ (a : ZMod 8)
    rw [hχ]
    simp only [GlobalTheoryTheory.kron]
    rw [boxes_kron_odd _ _ ha, jacobiSym.at_two (Nat.odd_iff.mpr ha)]

private theorem boxq_of_pair {M : ℕ} {eps Y X : ℝ} {q d : ℕ} (hM : 0 < M) (h : PairGood M eps Y X q d) : Boxq Y eps q d := by
  have hw := h.pair
  have hq4 : q % 4 = 3 := by have := hw.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hw.d_mod; omega
  have hone : ∀ a : ℕ, PChar.one.val a = 1 := fun a => by
    show (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
    rw [Subsingleton.elim (a : ZMod 1) 1, map_one]
  have hr1 : PChar.one.IsReal := by
    intro a
    show ((1 : DirichletCharacter ℂ 1) a).im = 0
    rw [Subsingleton.elim (α := ZMod 1) a 1, map_one]
    simp
  have h81 : PChar.one.N ∣ 8 := by
    show (1 : ℕ) ∣ 8
    exact one_dvd 8
  obtain ⟨ρ, hρr, hρN, hρv⟩ := real_character_mod_eight
  have hP : ∀ a : ℕ, a % 2 = 1 → GlobalTheoryTheory.psDir q a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) :=
    fun a ha => boxes_kron_neg q a hq4 ha
  have hC : ∀ a : ℕ, a % 2 = 1 → GlobalTheoryTheory.chDir d a = ((jacobiSym (a : ℤ) d : ℤ) : ℂ) :=
    fun a ha => boxes_kron_neg d a hd4 ha
  unfold Formalism.MainNotions.Inhab.Boxq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine boxes_core hM h PChar.one hr1 h81 1 0 (Or.inl (by decide)) _ (fun a ha => ?_) _ (by simp)
    rw [hP a ha]
    simp only [tw, hone, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine boxes_core hM h ρ hρr hρN 1 0 (Or.inl (by decide)) _ (fun a ha => ?_) _ (by simp)
    rw [hP a ha, hρv a ha]
    simp only [tw, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine boxes_core hM h PChar.one hr1 h81 0 1 (Or.inr (by decide)) _ (fun a ha => ?_) _ (by simp)
    rw [hC a ha]
    simp only [tw, hone, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine boxes_core hM h ρ hρr hρN 0 1 (Or.inr (by decide)) _ (fun a ha => ?_) _ (by simp)
    rw [hC a ha, hρv a ha]
    simp only [tw, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine boxes_core hM h PChar.one hr1 h81 1 1 (Or.inl (by decide)) _ (fun a ha => ?_) _ (by simp)
    rw [hC a ha, hP a ha]
    simp only [tw, hone, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine boxes_core hM h ρ hρr hρN 1 1 (Or.inl (by decide)) _ (fun a ha => ?_) _ (by simp)
    rw [hρv a ha, hC a ha, hP a ha]
    simp only [tw, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring

private theorem qdRows_kron_odd {p d : ℕ} (hp : ¬ 2 ∣ p) (h : p ∣ d + 1) : GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1 := by
  rw [boxes_kron_odd _ _ (by omega)]
  have hm : (-(d : ℤ)) % (p : ℤ) = 1 % (p : ℤ) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    have hd : (p : ℤ) ∣ ((d + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have e : -(d : ℤ) - 1 = -((d + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact dvd_neg.mpr hd
  rw [jacobiSym.mod_left' hm, jacobiSym.one_left]

private theorem qdRows_kron_two {d : ℕ} (h : d % 16 = 7) : GlobalTheoryTheory.kronSym (-(d : ℤ)) 2 = 1 := by
  have hf : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  simp only [GlobalTheoryTheory.kronSym, GlobalTheoryTheory.kron2, hf]
  have h1 : (-(d : ℤ)) % 2 ≠ 0 := by omega
  have h2 : (-(d : ℤ)) % 8 = 1 := by omega
  have h3 : (d : ℤ) % 2 = 1 := by omega
  norm_num [h1, h2, h3, jacobiSym.one_right]

private theorem qdRows_lo {z : ℝ} {n : ℕ} (hn : 0 < n) (h : z / 2 < Real.log n) : Real.sqrt (Real.exp z) < n := by
  rw [← Real.exp_half]
  calc Real.exp (z / 2) < Real.exp (Real.log n) := Real.exp_lt_exp.mpr h
    _ = n := Real.exp_log (by exact_mod_cast hn)

private theorem qdRows_up {z : ℝ} {n : ℕ} (hn : 0 < n) (h : Real.log n ≤ z) : (n : ℝ) ≤ Real.exp z := by
  calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log (by exact_mod_cast hn)).symm
    _ ≤ Real.exp z := Real.exp_le_exp.mpr h

private theorem pairRow_of_pair {R : Ranks} (H : Host R) {eps Y : ℝ} (h : WinPair eps Y H.q H.d)
    (hN : Real.log (H.QS * H.q * H.d) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2) : PairRow Y eps H := by
  have hq := h.q_prime
  have hd := h.d_prime
  have hqm := h.q_mod
  unfold GlobalTheory.EX.PairRow
  refine ⟨hq, hqm, ?_, ?_, hd, h.d_mod, ?_, ?_, ?_, ?_, hN⟩
  · exact qdRows_lo hq.pos h.q_lo
  · exact qdRows_up hq.pos h.q_up
  · exact qdRows_lo hd.pos h.d_lo
  · exact qdRows_up hd.pos h.d_up
  · exact qdRows_kron_odd (by omega) h.d_q
  · intro p hp hpY
    by_cases hp2 : p = 2
    · subst hp2
      exact qdRows_kron_two h.d_mod
    · exact qdRows_kron_odd (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm)
        (h.d_small p hp hp2 hpY)

private theorem qdq_core {M : ℕ} {eps Y x : ℝ} {q d : ℕ} (he : 0 < eps) (hx : 1 ≤ x) (hY : Y ≤ x)
    (h : PairGood M eps Y x q d) (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (f : ℕ → ℂ)
    (hf : ∀ a : ℕ, a % 2 = 1 → f a = tw (fun _ => 1) q d i j a) : BoundsAtX x eps 4 f (8 * q * d) := by
  intro N _ χ hind
  obtain ⟨hprim, hval⟩ := hind
  have hodd : ∀ a : ℕ, a.Coprime 2 → a % 2 = 1 := by
    intro a ha
    rcases Nat.even_or_odd a with ⟨k, hk⟩ | ho
    · exfalso
      have h2g : 2 ∣ Nat.gcd a 2 := Nat.dvd_gcd ⟨k, by omega⟩ dvd_rfl
      rw [ha] at h2g
      omega
    · exact Nat.odd_iff.mp ho
  have hind' : An.Induces χ (tw (fun a => (1 : DirichletCharacter ℂ M) a) q d i j) (2 * M * q * d) := by
    unfold An.Induces
    refine ⟨hprim, fun a ha => ?_⟩
    have h2 : a.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨M * q * d, by ring⟩ ha
    have hqa : a.Coprime q := Nat.Coprime.coprime_dvd_right ⟨2 * M * d, by ring⟩ ha
    have hda : a.Coprime d := Nat.Coprime.coprime_dvd_right ⟨2 * M * q, by ring⟩ ha
    have hMa : a.Coprime M := Nat.Coprime.coprime_dvd_right ⟨2 * q * d, by ring⟩ ha
    have h8a : a.Coprime (8 * q * d) := by
      have e8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [e8]
      exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 h2) hqa) hda
    rw [hval a h8a, hf a (hodd a h2)]
    have h1 : (1 : DirichletCharacter ℂ M) (a : ZMod M) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime a M).mpr hMa)
    simp only [tw, h1]
  obtain ⟨hg, hl⟩ := h.bounds 1 i j hij N χ hind' x hY le_rfl
  refine ⟨?_, hl⟩
  have e : GlobalTheoryTheory.gChi χ x = An.gChi χ x := rfl
  rw [e]
  refine le_trans hg ?_
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

private theorem qdq_of_pair {M : ℕ} {eps Y x : ℝ} {q d : ℕ} (he : 0 < eps) (hx : 1 ≤ x) (hY : Y ≤ x)
    (h : PairGood M eps Y x q d) : QDq x eps 4 q d := by
  have hw := h.pair
  have hq4 : q % 4 = 3 := by have := hw.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hw.d_mod; omega
  have hP : ∀ a : ℕ, a % 2 = 1 → GlobalTheoryTheory.psDir q a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) :=
    fun a ha => boxes_kron_neg q a hq4 ha
  have hC : ∀ a : ℕ, a % 2 = 1 → GlobalTheoryTheory.chDir d a = ((jacobiSym (a : ℤ) d : ℤ) : ℂ) :=
    fun a ha => boxes_kron_neg d a hd4 ha
  unfold Formalism.MainNotions.Inhab.QDq
  refine ⟨?_, ?_, ?_⟩
  · refine qdq_core he hx hY h 1 0 (Or.inl (by decide)) _ (fun a ha => ?_)
    rw [hP a ha]
    simp only [tw, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine qdq_core he hx hY h 0 1 (Or.inr (by decide)) _ (fun a ha => ?_)
    rw [hC a ha]
    simp only [tw, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring
  · refine qdq_core he hx hY h 1 1 (Or.inl (by decide)) _ (fun a ha => ?_)
    rw [hC a ha, hP a ha]
    simp only [tw, Fin.val_one, Fin.val_zero, pow_one, pow_zero]
    try ring

private theorem mul_le_exp_of_le_div_sq {eps C l : ℝ} (he : 0 < eps) (hC : 1 ≤ C) (hl : 41000 * C / eps ^ 2 ≤ l) :
    820 * C * l ≤ Real.exp (l * (eps / 5)) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by positivity) hl
  have hy0 : 0 ≤ l * (eps / 5) := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have h1 : 41000 * C ≤ l * eps ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hl
  have h2 : 41000 * C * l ≤ l * eps ^ 2 * l := mul_le_mul_of_nonneg_right h1 hl0.le
  have h3 : 820 * C * l ≤ (l * (eps / 5)) ^ 2 / 2 := by nlinarith
  linarith

theorem UpperTheory.Top.pairRows :
    ∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x →
      RankVal s R → HostConst s C0 H → 0 < M → PairWin s Y → PairGood M eps Y s.x H.q H.d →
      PairRow Y eps H ∧ QDq s.x eps 4 H.q H.d ∧ Boxq Y eps H.q H.d ∧ (4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) := by
  intro eps C0 he he1
  refine ⟨Real.exp (max C0 1 * max 2 (41000 * max C0 1 / eps ^ 2)), ?_⟩
  intro s R H M Y hs hx0 hRV hHC hM hPW hPG
  have hw := hPG.pair
  have hx1 : 1 < s.x := s.one_lt_alt
  have hJ1 : 1 ≤ s.J := s.one_le_J
  have hJC : s.J ≤ C0 := hHC.1
  have hC1 : 1 ≤ C0 := le_trans hJ1 hJC
  have hY1 : 1 < Y := hPW.one_lt
  have hYx : Y ≤ s.x := hPW.2
  refine ⟨?_, qdq_of_pair he hx1.le hYx hPG, boxq_of_pair hM hPG, H.qd_big⟩
  apply pairRow_of_pair H hw
  have hl0 : 0 < Real.log Y := Real.log_pos hY1
  have hKL : max C0 1 * max 2 (41000 * max C0 1 / eps ^ 2) ≤ Real.log s.x := by
    have := Real.log_le_log (Real.exp_pos _) hx0
    rwa [Real.log_exp] at this
  rw [max_eq_left hC1] at hKL
  have hlx : Real.log s.x ≤ C0 * Real.log Y := by
    have h1 := hPW.log_div_le
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith [mul_le_mul_of_nonneg_left hJC hl0.le]
  have hLl : max 2 (41000 * C0 / eps ^ 2) ≤ Real.log Y :=
    le_of_mul_le_mul_left (by linarith) (by linarith : (0 : ℝ) < C0)
  have hl2 : 2 ≤ Real.log Y := le_trans (le_max_left _ _) hLl
  have hlb : 41000 * C0 / eps ^ 2 ≤ Real.log Y := le_trans (le_max_right _ _) hLl
  have hT : 820 * C0 * Real.log Y ≤ Y ^ (eps / 5) := by
    have := mul_le_exp_of_le_div_sq he hC1 hlb
    rw [Real.rpow_def_of_pos (by linarith)]
    exact this
  have hQS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hq0 : (0 : ℝ) < H.q := by exact_mod_cast hw.q_prime.pos
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast hw.d_prime.pos
  have hxp : (0 : ℝ) < s.x ^ (9 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hQSle : (H.QS : ℝ) ≤ C0 * (2 * s.x ^ (9 / 4 : ℝ)) :=
    le_trans hHC.2.2 (mul_le_mul_of_nonneg_left hRV.n_le' (by linarith))
  have hlogQS : Real.log H.QS ≤ 2 * C0 + 9 / 4 * Real.log s.x := by
    have h1 := Real.log_le_log hQS0 hQSle
    rw [Real.log_mul (by linarith) (ne_of_gt (by positivity)), Real.log_mul (by norm_num) (ne_of_gt hxp),
      Real.log_rpow (by linarith)] at h1
    have h2 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < C0)
    have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  rw [Real.log_mul (ne_of_gt (mul_pos hQS0 hq0)) (ne_of_gt hd0), Real.log_mul (ne_of_gt hQS0) (ne_of_gt hq0)]
  have k1 : 820 * C0 * Real.log Y * (Real.log Y ^ 2 - 1) ≤ Y ^ (eps / 5) * (Real.log Y ^ 2 - 1) :=
    mul_le_mul_of_nonneg_right hT (by nlinarith)
  have k2 : 3 ≤ Real.log Y ^ 2 - 1 := by nlinarith
  have k3 : 820 * C0 * Real.log Y * 3 ≤ 820 * C0 * Real.log Y * (Real.log Y ^ 2 - 1) :=
    mul_le_mul_of_nonneg_left k2 (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hl0.le)
  have k4 : 2 * C0 ≤ C0 * Real.log Y := by nlinarith
  linarith [hw.q_up, hw.d_up]
