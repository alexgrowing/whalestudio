import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaRowStrictMono

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qa_S {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : ℕ := ∑ b : Fin n with b ≤ a, m (b, p)

lemma qa_S_mono {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (p : Fin n) {a a' : Fin n} (h : a ≤ a') :
    qa_S m a p ≤ qa_S m a' p := by
  unfold qa_S
  apply Finset.sum_le_sum_of_subset
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact hb.trans h

lemma qa_S_le {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : qa_S m a p ≤ ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma qa_S_last {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (p : Fin n) :
    qa_S m (lastIdx n) p = ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and, iff_true]
  rw [Fin.le_def]
  have := b.2
  simp only [lastIdx]
  omega

lemma qa_Slt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) :
    (∑ b : Fin n with b < a, m (b, p)) = 0 ∨ ∃ b, b < a ∧ (∑ b : Fin n with b < a, m (b, p)) = qa_S m b p := by
  obtain ⟨a, ha⟩ := a
  cases a with
  | zero =>
    left
    apply Finset.sum_eq_zero
    intro b hb
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hb
    omega
  | succ k =>
    right
    refine ⟨⟨k, by omega⟩, by simp [Fin.lt_def], ?_⟩
    unfold qa_S
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def, Fin.le_def]
    omega

lemma qa_of_cum {n : ℕ} (m m' : Fin n × Fin n →₀ ℕ) (h : ∀ a p, qa_S m a p = qa_S m' a p) : m = m' := by
  ext ⟨a, p⟩
  have hsplit : ∀ (m : Fin n × Fin n →₀ ℕ), qa_S m a p = m (a, p) + ∑ b : Fin n with b < a, m (b, p) := by
    intro m
    unfold qa_S
    have : (univ.filter fun b : Fin n => b ≤ a) = insert a (univ.filter fun b : Fin n => b < a) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      exact le_iff_eq_or_lt
    rw [this, Finset.sum_insert (by simp)]
  have h1 := h a p
  rw [hsplit m, hsplit m'] at h1
  rcases qa_Slt m a p with h0 | ⟨b, hb, h2⟩
  · rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · omega
    ·
      have h3 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b' p
      omega
  · have h3 : qa_S m' b p ≤ ∑ b : Fin n with b < a, m' (b, p) := by
      unfold qa_S
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact lt_of_le_of_lt hx hb
    rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · have := h b p
      omega
    · have h4 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b p
      have := h b' p
      omega

def qa_g {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n) : Fin n :=
  if h : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n then
    ⟨(univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card, h⟩ else lastIdx n

lemma qa_g_le_iff {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n)
    (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ)) (a : Fin n) : qa_g m k p ≤ a ↔ k ≤ qa_S m a p := by
  have hl := qa_lower_iff (fun a : Fin n => (qa_S m a p : ℤ) < k)
    (fun q q' hqq hq => lt_of_le_of_lt (by exact_mod_cast qa_S_mono m p hqq) hq)
  have hn : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n := by
    have h1 := hl (lastIdx n)
    rw [qa_S_last] at h1
    have h2 : ¬ (lastIdx n).val < (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card :=
      fun hh => absurd (h1.mpr hh) (not_lt.mpr hk)
    have h3 : (lastIdx n).val = n - 1 := rfl
    have := NeZero.pos n
    omega
  unfold qa_g
  rw [dif_pos hn, Fin.le_def]
  have h1 := hl a
  constructor
  · intro h
    by_contra hc
    have := h1.mp (not_le.mp hc)
    simp only at h
    omega
  · intro h
    by_contra hc
    have := h1.mpr (not_le.mp hc)
    omega

lemma qa_last_le {n : ℕ} [NeZero n] (p : Fin n) : p ≤ lastIdx n := by
  rw [Fin.le_def]
  have := p.2
  simp only [lastIdx]
  omega

lemma qa_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (p : Fin n) :
    (qa_nu mu p : ℤ) = mu p - mu (lastIdx n) := by
  unfold qa_nu
  have : mu (lastIdx n) ≤ mu p := hmu (qa_last_le p)
  omega

lemma qa_nu_antitone {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) : Antitone (qa_nu mu) := by
  intro p p' h
  have := hmu h
  unfold qa_nu
  omega

lemma qa_g_step {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (k : ℤ) (hk1 : 1 ≤ k)
    (p p' : Fin n) (hpp : p'.val = p.val + 1) (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ))
    (hk' : k ≤ (∑ b : Fin n, m (b, p') : ℕ)) : qa_g m k p < qa_g m k p' := by
  have h1 : k ≤ qa_S m (qa_g m k p') p' := (qa_g_le_iff m k p' hk' _).mp le_rfl
  have h2 : qa_S m (qa_g m k p') p' ≤ 0 + ∑ b : Fin n with b < qa_g m k p', m (b, p) :=
    hint p p' hpp (qa_g m k p')
  by_contra hc
  rcases qa_Slt m (qa_g m k p') p with h0 | ⟨b, hb, h3⟩
  · omega
  · have h4 : ¬ qa_g m k p ≤ b := fun hh => hc (lt_of_le_of_lt hh hb)
    rw [qa_g_le_iff m k p hk] at h4
    omega

lemma qa_g_lt {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (ν : Fin n → ℕ)
    (hν : Antitone ν) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = ν t) (k : ℤ) (hk1 : 1 ≤ k) :
    ∀ (d : ℕ) (p p' : Fin n), p'.val = p.val + d + 1 → k ≤ ν p' → qa_g m k p < qa_g m k p' := by
  intro d
  induction d with
  | zero =>
    intro p p' hpp hk
    have h1 : ν p' ≤ ν p := hν (by rw [Fin.le_def]; omega)
    exact qa_g_step m hint k hk1 p p' (by omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)
  | succ d ih =>
    intro p p' hpp hk
    have hlt : p.val + d + 1 < n := by have := p'.2; omega
    have h1 : ν p' ≤ ν ⟨p.val + d + 1, hlt⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    refine (ih p ⟨p.val + d + 1, hlt⟩ rfl (by omega)).trans ?_
    exact qa_g_step m hint k hk1 _ p' (by simp only; omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)

lemma qa_fill_exists {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hint : Formalism.GradedWeylDivisibility.Interlaced m) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) :
    ∃ I : TIdx mu, ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
  have hf : ∀ c : ↥(TCols mu), StrictMono fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
    intro c q q' hqq
    have hc := Finset.mem_Ioc.mp c.2
    rw [Fin.lt_def] at hqq
    refine qa_g_lt m hint (qa_nu mu) (qa_nu_antitone hmu) hcol _ (by omega) (q'.val - q.val - 1) _ _ ?_ ?_
    · simp only [Fin.val_castLE]; omega
    · rw [qa_nu_cast hmu]
      have := (qa_lt_colH hmu c (Fin.castLE (colH_le mu c) q')).mp q'.2
      omega
  refine ⟨fun c => ⟨univ.map ⟨_, (hf c).injective⟩, by simp⟩, fun c q => ?_⟩
  have := Finset.orderEmbOfFin_unique (s := univ.map ⟨_, (hf c).injective⟩) (by simp) (f := fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) (by simp) (hf c)
  exact (congrFun this q).symm

lemma qa_fill_cnt {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q))
    (c : ↥(TCols mu)) (a p : Fin n) :
    p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p := by
  have hc := Finset.mem_Ioc.mp c.2
  have key : ∀ hp : p.val < colH mu c, (p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p) := by
    intro hp
    have h1 := qa_row_le_iff I c ⟨p.val, hp⟩ a
    rw [hI] at h1
    have h2 : Fin.castLE (colH_le mu c) ⟨p.val, hp⟩ = p := Fin.ext rfl
    rw [h2, qa_g_le_iff] at h1
    · exact h1.symm
    · rw [hcol, qa_nu_cast hmu]
      have := (qa_lt_colH hmu c p).mp hp
      omega
  constructor
  · intro h
    exact (key (h.trans_le (qa_cnt_le I c a))).mp h
  · intro h
    have h1 := qa_S_le m a p
    rw [hcol] at h1
    have h2 := qa_nu_cast hmu p
    have hp : p.val < colH mu c := (qa_lt_colH hmu c p).mpr (by omega)
    exact (key hp).mpr h

lemma qa_fill_std {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) : StdT I := by
  intro c hc a
  change qa_cnt I ⟨(c : ℤ) + 1, hc⟩ a ≤ qa_cnt I c a
  by_contra hlt
  have hlt := not_le.mp hlt
  have hn : qa_cnt I c a < n := hlt.trans_le ((qa_cnt_le I _ a).trans (colH_le mu _))
  have h1 := (qa_fill_cnt hmu m hcol I hI ⟨(c : ℤ) + 1, hc⟩ a ⟨qa_cnt I c a, hn⟩).mp hlt
  have h2 := (qa_fill_cnt hmu m hcol I hI c a ⟨qa_cnt I c a, hn⟩).mpr (by simp only at h1; omega)
  exact lt_irrefl _ h2

lemma qa_fill_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) :
    qa_exp I = m := by
  classical
  apply qa_of_cum
  intro a p
  change ∑ b : Fin n with b ≤ a, qa_exp I (b, p) = qa_S m a p
  rw [qa_cum, qa_card_sub]
  have h1 := qa_S_le m a p
  rw [hcol] at h1
  have h2 := qa_nu_cast hmu p
  have h3 : mu p ≤ mu 0 := hmu (Fin.zero_le p)
  have : ((TCols mu).filter fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) =
      Finset.Ioc (mu (lastIdx n)) (mu (lastIdx n) + qa_S m a p) := by
    ext d
    simp only [mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, h, hp⟩
      have := (qa_fill_cnt hmu m hcol I hI ⟨d, h⟩ a p).mp hp
      have hd' := Finset.mem_Ioc.mp hd
      simp only at this
      omega
    · rintro ⟨hd1, hd2⟩
      have hd : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd1, by omega⟩
      exact ⟨hd, hd, (qa_fill_cnt hmu m hcol I hI ⟨d, hd⟩ a p).mpr (by simp only; omega)⟩
  rw [this, Int.card_Ioc]
  simp

theorem qa_exp_surj {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hm : m ∈ Formalism.GradedWeylDivisibility.ssIdx n n (qa_nu mu)) : ∃ I : TIdx mu, StdT I ∧ qa_exp I = m := by
  obtain ⟨I, hI⟩ := qa_fill_exists hmu m hm.1 hm.2
  exact ⟨I, qa_fill_std hmu m hm.2 I hI, qa_fill_exp hmu m hm.2 I hI⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
