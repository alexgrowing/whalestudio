import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestWeightSpaceFinite

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_lastIdx (m : ℕ) : lastIdx (m + 1) = Fin.last m := rfl

section Cols

variable {m : ℕ} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

lemma qr_colH_le (hi : Interl lam nu) (c : ℤ) : colH nu c ≤ colH lam c := by
  unfold colH
  rw [← Finset.card_map Fin.castSuccEmb]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha.trans (hi a).1

lemma qr_colH_le' (hi : Interl lam nu) (c : ℤ) : colH lam c ≤ colH nu c + 1 := by
  unfold colH
  rw [← Finset.card_map (Fin.succEmb m)]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le (0 : Fin (m + 1)) _)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  induction x using Fin.cases with
  | zero => left; rfl
  | succ a => right; exact ⟨a, hx.trans (hi a).2, rfl⟩

lemma qr_colH_eq (hi : Interl lam nu) (c : ℤ) :
    colH lam c = colH nu c + if colH lam c = colH nu c + 1 then 1 else 0 := by
  have h1 := qr_colH_le hi c
  have h2 := qr_colH_le' hi c
  split_ifs with h <;> omega

lemma qr_sum_colH {n : ℕ} (mu : Fin n → ℤ) (L U : ℤ) (h : ∀ a, L ≤ mu a ∧ mu a ≤ U) :
    ∑ c ∈ Finset.Ioc L U, (colH mu c : ℤ) = ∑ a, (mu a - L) := by
  have h1 : ∀ c, (colH mu c : ℤ) = ∑ a, if c ≤ mu a then 1 else 0 := by
    intro c
    rw [colH, Finset.card_filter]; push_cast; rfl
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (Finset.Ioc L U).filter (fun c => c ≤ mu a) = Finset.Ioc L (mu a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have := (h a).2
    constructor
    · rintro ⟨⟨h3, _⟩, h4⟩; exact ⟨h3, h4⟩
    · rintro ⟨h3, h4⟩; exact ⟨⟨h3, h4.trans this⟩, h4⟩
  rw [h2, Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.2 (h a).1)]

end Cols

section J

variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

lemma qr_le_last (hn : Dominant nu) (a : Fin m) : nu (lastIdx m) ≤ nu a := by
  apply hn
  rw [Fin.le_def]
  show a.1 ≤ m - 1
  have := a.2
  omega

lemma qr_le_zero {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hn : Dominant mu) (a : Fin n) : mu a ≤ mu 0 := hn (Fin.zero_le a)

lemma qr_lam_last_le (hi : Interl lam nu) : lam (Fin.last m) ≤ nu (lastIdx m) := by
  have h := (hi (lastIdx m)).2
  have h1 : (lastIdx m).succ = Fin.last m := by
    apply Fin.ext
    show m - 1 + 1 = m
    have := NeZero.pos m
    omega
  rwa [h1] at h

lemma qr_nu_zero_le (hi : Interl lam nu) : nu 0 ≤ lam 0 := (hi 0).1

lemma qr_TCols_sub (hi : Interl lam nu) {c : ℤ} (hc : c ∈ TCols nu) : c ∈ TCols lam := by
  simp only [TCols, Finset.mem_Ioc, qr_lastIdx] at hc ⊢
  exact ⟨lt_of_le_of_lt (qr_lam_last_le hi) hc.1, hc.2.trans (qr_nu_zero_le hi)⟩

lemma qr_colH_low (hn : Dominant nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) : colH nu c = m := by
  rw [colH, Finset.filter_true_of_mem]
  · simp
  · intro a _; exact hc.trans (qr_le_last hn a)

lemma qr_colH_high (hn : Dominant nu) {c : ℤ} (hc : nu 0 < c) : colH nu c = 0 := by
  rw [colH, Finset.filter_false_of_mem]
  · simp
  · intro a _; exact not_le.2 (lt_of_le_of_lt (qr_le_zero hn a) hc)

lemma qr_subsing (hn : Dominant nu) {c : ℤ} (hc : c ∉ TCols nu) :
    Subsingleton {S : Finset (Fin m) // S.card = colH nu c} := by
  simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt, not_le] at hc
  constructor
  rintro ⟨S, hS⟩ ⟨S', hS'⟩
  apply Subtype.ext
  show S = S'
  rcases hc with hc | hc
  · rw [qr_colH_low hn hc] at hS hS'
    rw [Finset.eq_univ_of_card S (by simpa using hS), Finset.eq_univ_of_card S' (by simpa using hS')]
  · rw [qr_colH_high hn hc] at hS hS'
    rw [Finset.card_eq_zero.1 hS, Finset.card_eq_zero.1 hS']

def qr_can (nu : Fin m → ℤ) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  ⟨(univ : Finset (Fin (colH nu c))).map (Fin.castLEEmb (colH_le nu c)), by simp⟩

def qr_base (I' : TIdx nu) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  if h : c ∈ TCols nu then I' ⟨c, h⟩ else qr_can nu c

lemma qr_base_can (c : ℤ) : qr_base (canT nu) c = qr_can nu c := by
  unfold qr_base
  split_ifs <;> rfl

lemma qr_base_mem (I' : TIdx nu) (c : ↥(TCols nu)) : qr_base I' c = I' c := by
  unfold qr_base
  rw [dif_pos c.2]

def qr_j (hi : Interl lam nu) (I' : TIdx nu) : TIdx lam := fun c =>
  ⟨qr_ext (colH lam c = colH nu c + 1) (qr_base I' c).1, by
    rw [qr_ext_card, (qr_base I' c).2]; exact (qr_colH_eq hi c).symm⟩

lemma qr_j_inj (hi : Interl lam nu) : Function.Injective (qr_j (lam := lam) hi) := by
  intro I' K' h
  funext c
  have h1 := congrArg Subtype.val (congrFun h ⟨c.1, qr_TCols_sub hi c.2⟩)
  have h2 := qr_ext_inj _ h1
  rw [qr_base_mem, qr_base_mem] at h2
  exact Subtype.ext h2

lemma qr_j_surj (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam)
    (hK : ∀ c : ↥(TCols lam), (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1)) :
    ∃ K' : TIdx nu, qr_j hi K' = K := by
  have hc : ∀ c : ↥(TCols lam), (univ.filter fun a : Fin m => a.castSucc ∈ (K c).1).card = colH nu c := by
    intro c
    have h1 := congrArg Finset.card (qr_ext_surj _ (K c).1 (hK c))
    rw [qr_ext_card, (K c).2] at h1
    have h2 := qr_colH_eq hi c
    omega
  refine ⟨fun c => ⟨_, hc ⟨c.1, qr_TCols_sub hi c.2⟩⟩, ?_⟩
  funext c
  apply Subtype.ext
  show qr_ext _ _ = _
  rw [qr_ext_surj _ (K c).1 (hK c)]
  congr 1
  by_cases h : c.1 ∈ TCols nu
  · rw [qr_base, dif_pos h]
  · have := qr_subsing hn h
    exact congrArg Subtype.val (Subsingleton.elim (qr_base _ c.1) ⟨_, hc c⟩)

lemma qr_can_sub (c : ℤ) : (qr_can nu (c + 1)).1 ⊆ (qr_can nu c).1 := by
  intro x hx
  simp only [qr_can, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le nu c)⟩, rfl⟩

lemma qr_j_can_std (hi : Interl lam nu) : StdT (qr_j (lam := lam) hi (canT nu)) := by
  intro c hc t
  show ((qr_ext _ (qr_base (canT nu) (c.1 + 1)).1).filter (· ≤ t)).card ≤
    ((qr_ext _ (qr_base (canT nu) c.1).1).filter (· ≤ t)).card
  rw [qr_base_can, qr_base_can]
  induction t using Fin.lastCases with
  | last =>
    rw [qr_filter_last, qr_filter_last, qr_ext_card, qr_ext_card, (qr_can nu _).2, (qr_can nu _).2,
      ← qr_colH_eq hi, ← qr_colH_eq hi]
    exact qc_colH_succ_le lam c
  | cast t =>
    rw [qr_filter_castSucc, qr_filter_castSucc, Finset.card_map, Finset.card_map]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (qr_can_sub c.1))

end J

end Formalism.InvariantFactorPaths.ColumnFamilies
