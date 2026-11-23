import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColumnKernelComponentsIntegral

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Deg

variable {R : Type*} [CommRing R] {N k : ℕ}

def HomD (d : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin k) R) : Prop :=
  ∀ m ∈ F.support, ∀ i, multideg m i = d i

lemma HomD.zero (d : Fin N → ℕ) : HomD d (0 : MvPolynomial (Fin N × Fin k) R) := by
  intro m hm
  simp at hm

lemma HomD.add {d : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (hG : HomD d G) :
    HomD d (F + G) := by
  intro m hm i
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hF m h i
  · exact hG m h i

lemma HomD.sum {ι' : Type*} {d : Fin N → ℕ} (s : Finset ι') (F : ι' → MvPolynomial (Fin N × Fin k) R)
    (h : ∀ a ∈ s, HomD d (F a)) : HomD d (∑ a ∈ s, F a) := by
  exact Finset.sum_induction F (HomD d) (fun a b ha hb => ha.add hb) (HomD.zero d) h

lemma multideg_add (a b : Fin N × Fin k →₀ ℕ) (i : Fin N) : multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

lemma HomD.mul {d d' : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (hG : HomD d' G) :
    HomD (d + d') (F * G) := by
  intro m hm i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul F G hm)
  rw [multideg_add, hF a ha i, hG b hb i, Pi.add_apply]

lemma HomD.one : HomD (0 : Fin N → ℕ) (1 : MvPolynomial (Fin N × Fin k) R) := by
  intro m hm i
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp [multideg]
  · exact absurd rfl hm

lemma HomD.pow {d : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (Q : ℕ) :
    HomD (Q • d) (F ^ Q) := by
  induction Q with
  | zero => rw [pow_zero, zero_smul]; exact HomD.one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hF

lemma HomD.sign {d : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin k) R} (hF : HomD d F) (n : ℕ) :
    HomD d ((-1) ^ n * F) := by
  have h1 : HomD (0 : Fin N → ℕ) (-1 : MvPolynomial (Fin N × Fin k) R) := by
    intro m hm
    rw [MvPolynomial.support_neg] at hm
    exact HomD.one m hm
  have h2 := (h1.pow n).mul hF
  rwa [smul_zero, zero_add] at h2

def eI (i : Fin N) : Fin N → ℕ := fun i' => if i' = i then 1 else 0

lemma colStep_HomD (c : ℤ) (hP hN : ℕ) (hne : hP ≠ hN) (i : Fin N) (d : Fin N → ℕ)
    (x : Fin k → MvPolynomial (Fin N × Fin k) R) (Kv : Finset (Fin k) → MvPolynomial (Fin N × Fin k) R)
    (hx : ∀ b, HomD (eI i) (x b)) (hK : ∀ J, HomD d (Kv J)) (J : Finset (Fin k)) :
    HomD (eI i + d) (colStep c hP hN x Kv J) := by
  have hw : HomD (eI i + d) (wedgeR x Kv J) := by
    unfold wedgeR
    exact HomD.sum _ _ fun m _ => ((hx m).sign _).mul (hK _)
  have hc : HomD (eI i + d) (contrR x Kv J) := by
    unfold contrR
    exact HomD.sum _ _ fun m _ => ((hx m).sign _).mul (hK _)
  unfold colStep
  split_ifs
  all_goals first | exact hw | exact hc | exact (hne (by omega)).elim

open Classical in

def dgS (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s : ℤ) : Fin N → ℕ :=
  fun i => if i.val < j ∧ IsUsed mu c i then p ^ (s - pos i).toNat else 0

private theorem pow_toNat_mul_pow_toNat_eq_of_le (p : ℕ) {u v w : ℤ} (h1 : u ≤ v) (h2 : v ≤ w) :
    p ^ (w - v).toNat * p ^ (v - u).toNat = p ^ (w - u).toNat := by
  rw [← pow_add]
  congr 1
  omega

private theorem dgS_eq_zero_of_none_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s : ℤ)
    (h : ∀ i : Fin N, i.val < j → ¬ IsUsed mu c i) : dgS p pos mu c j s = 0 := by
  funext i
  simp only [dgS, Pi.zero_apply]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact h i h1 h2

private theorem dgS_succ_eq_of_not_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j < N)
    (hu : ¬ IsUsed mu c ⟨j, hj⟩) (s : ℤ) : dgS p pos mu c (j + 1) s = dgS p pos mu c j s := by
  funext i
  simp only [dgS]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    apply h2
    refine ⟨?_, h1.2⟩
    by_cases h : i.val < j
    · exact h
    · have e : i = ⟨j, hj⟩ := Fin.ext (show i.val = j by have := h1.1; omega)
      subst e
      exact absurd h1.2 hu
  · exfalso
    exact h1 ⟨Nat.lt_succ_of_lt h2.1, h2.2⟩
  · rfl

private theorem eI_eq_dgS_succ_of_first_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j < N)
    (hu : IsUsed mu c ⟨j, hj⟩) (h : ∀ i : Fin N, i.val < j → ¬ IsUsed mu c i) :
    eI ⟨j, hj⟩ + 1 • (0 : Fin N → ℕ) = dgS p pos mu c (j + 1) (pos ⟨j, hj⟩) := by
  funext i
  simp only [Pi.add_apply, smul_zero, Pi.zero_apply, add_zero, eI, dgS]
  by_cases hij : i.val = j
  · have e : i = ⟨j, hj⟩ := Fin.ext hij
    subst e
    simp [hu]
  · have hne : i ≠ ⟨j, hj⟩ := fun e => hij (by rw [e])
    rw [if_neg hne, if_neg]
    rintro ⟨h1, h2⟩
    exact h i (by omega) h2

private theorem eI_add_pow_smul_dgS_eq_dgS_succ_of_used (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j < N)
    (sl : ℤ) (hu : IsUsed mu c ⟨j, hj⟩) (hsl : sl ≤ pos ⟨j, hj⟩)
    (hle : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ sl) :
    eI ⟨j, hj⟩ + p ^ (pos ⟨j, hj⟩ - sl).toNat • dgS p pos mu c j sl = dgS p pos mu c (j + 1) (pos ⟨j, hj⟩) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eI, dgS]
  by_cases hij : i.val = j
  · have e : i = ⟨j, hj⟩ := Fin.ext hij
    subst e
    simp [hu]
  · have hne : i ≠ ⟨j, hj⟩ := fun e => hij (by rw [e])
    rw [if_neg hne, zero_add]
    by_cases hU : IsUsed mu c i
    · by_cases hlt : i.val < j
      · rw [if_pos ⟨hlt, hU⟩, if_pos ⟨by omega, hU⟩]
        exact pow_toNat_mul_pow_toNat_eq_of_le p (hle i hlt hU) hsl
      · rw [if_neg (fun h => hlt h.1), if_neg (fun h => by have := h.1; omega)]
        simp
    · rw [if_neg (fun h => hU h.2), if_neg (fun h => hU h.2)]
      simp

private theorem pow_smul_dgS_eq_dgS_of_le (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s sl : ℤ)
    (hsl : sl ≤ s) (hle : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ sl) :
    p ^ (s - sl).toNat • dgS p pos mu c j sl = dgS p pos mu c j s := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, dgS]
  split_ifs with h
  · exact pow_toNat_mul_pow_toNat_eq_of_le p (hle i h.1 h.2) hsl
  · simp

private theorem homD_KKs_and_slot_properties (p : ℕ) (x : Fin N → Fin k → MvPolynomial (Fin N × Fin k) R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hmono : Monotone pos) (hx : ∀ i b, HomD (eI i) (x i b)) (j : ℕ) :
    j ≤ N →
      ((KKs p x pos mu c j).2 = none →
        (∀ i : Fin N, i.val < j → ¬ IsUsed mu c i) ∧ ∀ J, HomD 0 ((KKs p x pos mu c j).1 J)) ∧
      (∀ sl, (KKs p x pos mu c j).2 = some sl →
        (∃ i₀ : Fin N, i₀.val < j ∧ IsUsed mu c i₀ ∧ pos i₀ = sl) ∧
        (∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ sl) ∧
        ∀ J, HomD (dgS p pos mu c j sl) ((KKs p x pos mu c j).1 J)) := by
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun J => ?_⟩, fun sl hsl => ?_⟩
    · simp only [KKs, extOne]
      split_ifs
      · exact HomD.one
      · exact HomD.zero _
    · simp [KKs] at hsl
  | succ j ih =>
    intro hj
    have hjN : j < N := hj
    obtain ⟨ihN, ihS⟩ := ih (Nat.le_of_lt hjN)
    have hmax : ∀ i : Fin N, i.val < j + 1 → pos i ≤ pos ⟨j, hjN⟩ :=
      fun i hi => hmono (Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hi))
    by_cases heq : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · have hu : ¬ IsUsed mu c ⟨j, hjN⟩ := fun h => h heq
      have hK : KKs p x pos mu c (j + 1) = KKs p x pos mu c j := by
        simp only [KKs, dif_pos hjN, if_pos heq]
      rw [hK]
      refine ⟨fun hn => ?_, fun sl hs => ?_⟩
      · obtain ⟨h1, h2⟩ := ihN hn
        refine ⟨fun i hi hU => ?_, h2⟩
        by_cases hij : i.val = j
        · have e : i = ⟨j, hjN⟩ := Fin.ext hij
          subst e
          exact hu hU
        · exact h1 i (by omega) hU
      · obtain ⟨⟨i₀, hi₀, hU₀, he₀⟩, h2, h3⟩ := ihS sl hs
        refine ⟨⟨i₀, by omega, hU₀, he₀⟩, fun i hi hU => ?_, ?_⟩
        · by_cases hij : i.val = j
          · have e : i = ⟨j, hjN⟩ := Fin.ext hij
            subst e
            exact absurd hU hu
          · exact h2 i (by omega) hU
        · intro J
          rw [dgS_succ_eq_of_not_used p pos mu c j hjN hu sl]
          exact h3 J
    · have hu : IsUsed mu c ⟨j, hjN⟩ := heq
      cases hst : (KKs p x pos mu c j).2 with
      | none =>
        obtain ⟨h1, h2⟩ := ihN hst
        have hK : KKs p x pos mu c (j + 1) =
            (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (x ⟨j, hjN⟩)
              (powC 1 (KKs p x pos mu c j).1), some (pos ⟨j, hjN⟩)) := by
          simp only [KKs, dif_pos hjN, if_neg heq, hst]
        rw [hK]
        refine ⟨fun hn => by simp at hn, fun sl hs => ?_⟩
        simp at hs
        subst hs
        refine ⟨⟨⟨j, hjN⟩, by simp, hu, rfl⟩, fun i hi _ => hmax i hi, fun J => ?_⟩
        rw [← eI_eq_dgS_succ_of_first_used p pos mu c j hjN hu h1]
        exact colStep_HomD c _ _ heq ⟨j, hjN⟩ _ _ _ (hx ⟨j, hjN⟩) (fun J => (h2 J).pow 1) J
      | some sl0 =>
        obtain ⟨⟨i₀, hi₀, hU₀, he₀⟩, h2, h3⟩ := ihS sl0 hst
        have hK : KKs p x pos mu c (j + 1) =
            (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (x ⟨j, hjN⟩)
              (powC (p ^ (pos ⟨j, hjN⟩ - sl0).toNat) (KKs p x pos mu c j).1), some (pos ⟨j, hjN⟩)) := by
          simp only [KKs, dif_pos hjN, if_neg heq, hst]
        rw [hK]
        refine ⟨fun hn => by simp at hn, fun sl hs => ?_⟩
        simp at hs
        subst hs
        have hsl : sl0 ≤ pos ⟨j, hjN⟩ := by rw [← he₀]; exact hmax i₀ (by omega)
        refine ⟨⟨⟨j, hjN⟩, by simp, hu, rfl⟩, fun i hi _ => hmax i hi, fun J => ?_⟩
        rw [← eI_add_pow_smul_dgS_eq_dgS_succ_of_used p pos mu c j hjN sl0 hu hsl h2]
        exact colStep_HomD c _ _ heq ⟨j, hjN⟩ _ _ _ (hx ⟨j, hjN⟩) (fun J => (h3 J).pow _) J

theorem ZZ_HomD (p : ℕ) (x : Fin N → Fin k → MvPolynomial (Fin N × Fin k) R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hmono : Monotone pos) (hx : ∀ i b, HomD (eI i) (x i b))
    (j : ℕ) (hj : j ≤ N) :
    ∀ s : ℤ, (∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ s) → ∀ J,
      HomD (dgS p pos mu c j s) (ZZ p x pos mu c j s J) := by
  intro s hs J
  obtain ⟨hN', hS⟩ := homD_KKs_and_slot_properties p x pos mu c hmono hx j hj
  cases hst : (KKs p x pos mu c j).2 with
  | none =>
    obtain ⟨h1, h2⟩ := hN' hst
    have hZ : ZZ p x pos mu c j s J = (KKs p x pos mu c j).1 J := by simp only [ZZ, hst]
    rw [hZ, dgS_eq_zero_of_none_used p pos mu c j s h1]
    exact h2 J
  | some sl =>
    obtain ⟨⟨i₀, hi₀, hU₀, he₀⟩, h2, h3⟩ := hS sl hst
    have hZ : ZZ p x pos mu c j s J = powC (p ^ (s - sl).toNat) (KKs p x pos mu c j).1 J := by
      simp only [ZZ, hst]
    have hsl : sl ≤ s := by rw [← he₀]; exact hs i₀ hi₀ hU₀
    rw [hZ, ← pow_smul_dgS_eq_dgS_of_le p pos mu c j s sl hsl h2]
    exact (h3 J).pow _

end Deg

section Clause2

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] {N k : ℕ}

lemma XC_HomD (i : Fin N) (a : Fin k) (t : KK O) :
    HomD (eI i) (X (i, a) * C t : MvPolynomial (Fin N × Fin k) (KK O)) := by
  intro m hm i'
  rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial] at hm
  have hm' := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm)
  subst hm'
  by_cases h : i' = i
  · subst h
    simp [multideg, eI, Finsupp.single_apply]
  · simp [multideg, eI, Finsupp.single_apply, h, Ne.symm h]

lemma letG_HomD (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (i : Fin N) (b : Fin k) :
    HomD (eI i) (letG p f (O := O) LL g i b) := by
  unfold letG
  split_ifs
  · exact HomD.sum _ _ fun a _ => by apply XC_HomD
  · exact HomD.sum _ _ fun a _ => by apply XC_HomD

theorem lifted_column_multidegree (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (z : ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hmono : Monotone LL.pos) (hz : ∀ i, LL.pos i ≤ z)
    (J : Finset (Fin k)) (m : Fin N × Fin k →₀ ℕ) (hm : m ∈ (KKc p f (O := O) LL g z mu c J).support) (i : Fin N)
    (hi : IsUsed mu c i) : multideg m i = p ^ (z - LL.pos i).toNat := by
  rw [KKc_eq] at hm
  have H := ZZ_HomD p (letG p f (O := O) LL g) LL.pos mu c hmono (fun i b => by apply letG_HomD) N le_rfl z
    (fun i _ _ => hz i) J m hm i
  rw [H]
  simp [dgS, i.isLt, hi]

end Clause2

end Formalism.MainNotions.LemmaBAlt
