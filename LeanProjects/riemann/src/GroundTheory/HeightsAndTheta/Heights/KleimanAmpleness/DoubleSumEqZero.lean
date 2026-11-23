import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace CellDSq

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

def rem (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) : ∀ k, Finset (ι k) :=
  Function.update I p.1 ((I p.1).erase p.2)

theorem sigma_rem (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) :
    Finset.univ.sigma (rem I p) = (Finset.univ.sigma I).erase p := by
  obtain ⟨k₀, i₀⟩ := p
  ext ⟨k, i⟩
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_erase, rem]
  by_cases hk : k = k₀
  · subst hk
    simp [Finset.mem_erase]
  · rw [Function.update_of_ne hk]
    simp [hk]

omit [Fintype K] in

theorem rem_rem_comm (I : ∀ k, Finset (ι k)) (p q : Σ k, ι k) :
    rem (rem I p) q = rem (rem I q) p := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', i'⟩ := q
  by_cases hk : k' = k
  · subst hk
    simp only [rem, Function.update_self, Function.update_idem, Finset.erase_right_comm]
  · simp only [rem]
    rw [Function.update_of_ne hk, Function.update_of_ne (Ne.symm hk),
      Function.update_comm (Ne.symm hk)]

omit [∀ k, LinearOrder (ι k)] in

theorem offset_update (I : ∀ k, Finset (ι k)) (k : K) (X : Finset (ι k)) :
    ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k X l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
  Finset.sum_congr rfl fun l hl => by
    rw [Function.update_of_ne (ne_of_lt (Finset.mem_filter.1 hl).2)]

theorem sign_swap_same {I : ∀ k, Finset (ι k)} {k : K} {i i' : ι k} (hi : i ∈ I k) (hlt : i < i') :
    faceSign I k i' * faceSign (rem I ⟨k, i'⟩) k i = -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k i') := by
  have h1 : ((I k).erase i').filter (· < i) = (I k).filter (· < i) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzi⟩; exact ⟨hz, hzi⟩
    · rintro ⟨hz, hzi⟩; exact ⟨⟨(hzi.trans hlt).ne, hz⟩, hzi⟩
  have h3 : i ∈ (I k).filter (· < i') := Finset.mem_filter.2 ⟨hi, hlt⟩
  have h2 : (((I k).erase i).filter (· < i')).card + 1 = ((I k).filter (· < i')).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold faceSign rem
  simp only [Function.update_self, offset_update]
  rw [h1, ← h2]
  ring

theorem sign_swap_lt {I : ∀ k, Finset (ι k)} {k k' : K} (i : ι k) (i' : ι k') (hi : i ∈ I k)
    (hk : k < k') (h2 : 2 ≤ (I k).card) :
    faceSign I k' i' * faceSign (rem I ⟨k', i'⟩) k i =
      -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k' i') := by
  have hmem : k ∈ Finset.univ.filter (· < k') := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
  have hoff : ∑ l ∈ Finset.univ.filter (· < k'), ((Function.update I k ((I k).erase i) l).card - 1) + 1 =
      ∑ l ∈ Finset.univ.filter (· < k'), ((I l).card - 1) := by
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, Function.update_self,
      Finset.sum_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)],
      Finset.card_erase_of_mem hi]
    omega
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((Function.update I k' ((I k').erase i') l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
    Finset.sum_congr rfl fun l hl => by
      rw [Function.update_of_ne (ne_of_lt ((Finset.mem_filter.1 hl).2.trans hk))]
  unfold faceSign rem
  simp only [Function.update_of_ne hk.ne, Function.update_of_ne hk.ne', hlow]
  rw [← hoff]
  ring

omit [Fintype K] in
theorem rem_apply_of_ne {I : ∀ k, Finset (ι k)} {k l : K} (i : ι k) (h : l ≠ k) :
    rem I ⟨k, i⟩ l = I l :=
  Function.update_of_ne h _ _

omit [Fintype K] in
theorem rem_apply_self (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) :
    rem I ⟨k, i⟩ k = (I k).erase i :=
  Function.update_self _ _ _

omit [Fintype K] [LinearOrder K] in
theorem two_le_card {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k)
    (h : ((I k).erase i).Nonempty) : 2 ≤ (I k).card := by
  have := h.card_pos
  rw [Finset.card_erase_of_mem hi] at this
  omega

theorem sign_swap {I : ∀ k, Finset (ι k)} {p q : Σ k, ι k} (hp : p.2 ∈ I p.1) (hq : q.2 ∈ I q.1)
    (hne : q ≠ p) (hJ : ∀ l, (rem (rem I p) q l).Nonempty) :
    faceSign I p.1 p.2 * faceSign (rem I p) q.1 q.2 =
      -(faceSign I q.1 q.2 * faceSign (rem I q) p.1 p.2) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', i'⟩ := q
  rcases lt_trichotomy k k' with h | rfl | h
  · have hb := hJ k
    rw [rem_apply_of_ne _ h.ne, rem_apply_self] at hb
    rw [sign_swap_lt i i' hp h (two_le_card hp hb), neg_neg]
  · have hii : i' ≠ i := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hii with h | h
    · exact sign_swap_same hq h
    · rw [sign_swap_same hp h, neg_neg]
  · have hb := hJ k'
    rw [rem_apply_self, rem_apply_of_ne _ h.ne] at hb
    exact sign_swap_lt i' i hq h (two_le_card hq hb)

theorem double_sum_eq_zero {Ω : Type} [AddCommGroup Ω] (I : ∀ k, Finset (ι k))
    (g : (∀ k, Finset (ι k)) → Ω) (hg : ∀ J, g J ≠ 0 → ∀ l, (J l).Nonempty) :
    ∑ k, ∑ i ∈ I k, faceSign I k i • ∑ k', ∑ i' ∈ rem I ⟨k, i⟩ k',
      faceSign (rem I ⟨k, i⟩) k' i' • g (rem (rem I ⟨k, i⟩) ⟨k', i'⟩) = 0 := by
  let f : (Σ _ : (Σ k, ι k), Σ k, ι k) → Ω := fun x =>
    (faceSign I x.1.1 x.1.2 * faceSign (rem I x.1) x.2.1 x.2.2) • g (rem (rem I x.1) x.2)
  have step : ∀ k, ∀ i ∈ I k, faceSign I k i • ∑ k', ∑ i' ∈ rem I ⟨k, i⟩ k',
      faceSign (rem I ⟨k, i⟩) k' i' • g (rem (rem I ⟨k, i⟩) ⟨k', i'⟩) =
        ∑ q ∈ (Finset.univ.sigma I).erase ⟨k, i⟩, f ⟨⟨k, i⟩, q⟩ := by
    intro k i _
    rw [← sigma_rem, Finset.sum_sigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl (step k),
    ← Finset.sum_sigma Finset.univ I (fun p => ∑ q ∈ (Finset.univ.sigma I).erase p, f ⟨p, q⟩),
    Finset.sum_sigma' (Finset.univ.sigma I) (fun p => (Finset.univ.sigma I).erase p) (fun p q => f ⟨p, q⟩)]
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hx
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
    simp only [f]
    rw [rem_rem_comm I q p]
    by_cases h0 : g (rem (rem I p) q) = 0
    · rw [h0, smul_zero, smul_zero, add_zero]
    · rw [sign_swap (Finset.mem_sigma.1 hp).2 (Finset.mem_sigma.1 hq).2 hne (hg _ h0), neg_smul]
      exact neg_add_cancel _
  · rintro ⟨p, q⟩ hx - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hx).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨p, q⟩ hx
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_sigma.2 ⟨hq, Finset.mem_erase.2 ⟨hne.symm, hp⟩⟩
  · rintro ⟨p, q⟩ -
    rfl

variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

open Classical in

def ext (m : ℕ) (t : Cell K ι m → Ω) (J : ∀ k, Finset (ι k)) : Ω :=
  if h : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = m then t ⟨J, h⟩ else 0

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] [∀ k, Fintype (ι k)] [Algebra S Ω] in
theorem ext_ne_zero {m : ℕ} (t : Cell K ι m → Ω) (J : ∀ k, Finset (ι k)) (h : ext m t J ≠ 0) :
    ∀ l, (J l).Nonempty := by
  unfold ext at h
  split_ifs at h with hc
  · exact hc.1
  · exact absurd rfl h

omit [∀ k, Fintype (ι k)] in
theorem cellD_apply (y : (Σ k, ι k) → Ω) (m : ℕ) (t : Cell K ι m → Ω) (J : Cell K ι (m + 1))
    (hJ : CellMeets y J.1) :
    cellD S y m t J = ∑ k, ∑ i ∈ J.1 k, faceSign J.1 k i • ext m t (rem J.1 ⟨k, i⟩) := by
  simp only [cellD, LinearMap.pi_apply, if_pos hJ, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  unfold ext rem
  by_cases h : (∀ l, (Function.update J.1 k ((J.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update J.1 k ((J.1 k).erase i) l).card - 1) = m
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, smul_zero]; rfl

omit [∀ k, Fintype (ι k)] in
theorem cellD_apply_not (y : (Σ k, ι k) → Ω) (m : ℕ) (t : Cell K ι m → Ω) (J : Cell K ι (m + 1))
    (hJ : ¬ CellMeets y J.1) : cellD S y m t J = 0 := by
  simp only [cellD, LinearMap.pi_apply, if_neg hJ, LinearMap.zero_apply]

omit [∀ k, Fintype (ι k)] [Fintype K] [Algebra S Ω] in

theorem meets_rem {y : (Σ k, ι k) → Ω} {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (p : Σ k, ι k) :
    CellMeets y (rem I p) := by
  obtain ⟨k, i⟩ := p
  intro l j hj
  by_cases hl : l = k
  · subst hl
    rw [rem_apply_self] at hj
    exact hI l j (Finset.mem_of_mem_erase hj)
  · rw [rem_apply_of_ne _ hl] at hj
    exact hI l j hj

omit [∀ k, Fintype (ι k)] [Algebra S Ω] in

theorem rem_isCell {m : ℕ} (J : Cell K ι (m + 1)) {k : K} {i : ι k} (hi : i ∈ J.1 k)
    (hne : ((J.1 k).erase i).Nonempty) :
    (∀ l, (rem J.1 ⟨k, i⟩ l).Nonempty) ∧ ∑ l, ((rem J.1 ⟨k, i⟩ l).card - 1) = m := by
  have hdeg := J.2.2
  have hk := two_le_card hi hne
  refine ⟨fun l => ?_, ?_⟩
  · by_cases hl : l = k
    · subst hl; rw [rem_apply_self]; exact hne
    · rw [rem_apply_of_ne _ hl]; exact J.2.1 l
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hdeg ⊢
    rw [rem_apply_self, Finset.card_erase_of_mem hi,
      Finset.sum_congr rfl fun l hl => by rw [rem_apply_of_ne _ (Finset.ne_of_mem_erase hl)]]
    omega

omit [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [LinearOrder K] [Algebra S Ω] in
theorem ext_of_empty {m : ℕ} (t : Cell K ι m → Ω) {J : ∀ k, Finset (ι k)} {k : K} (h : J k = ∅) :
    ext m t J = 0 := by
  unfold ext
  rw [dif_neg]
  rintro ⟨hc, -⟩
  simpa [h] using hc k

end CellDSq

open CellDSq in

theorem CellDSq.proof : CellDSq.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y n s
  funext I
  show cellD S y (n + 1) (cellD S y n s) I = 0
  by_cases hI : CellMeets y I.1
  · rw [cellD_apply S y (n + 1) _ I hI]
    have key : ∀ k, ∀ i ∈ I.1 k, ext (n + 1) (cellD S y n s) (rem I.1 ⟨k, i⟩) =
        ∑ k', ∑ i' ∈ rem I.1 ⟨k, i⟩ k',
          faceSign (rem I.1 ⟨k, i⟩) k' i' • ext n s (rem (rem I.1 ⟨k, i⟩) ⟨k', i'⟩) := by
      intro k i hi
      by_cases hne : ((I.1 k).erase i).Nonempty
      · have hc := rem_isCell I hi hne
        rw [ext, dif_pos hc, cellD_apply S y n s ⟨_, hc⟩ (meets_rem hI _)]
      · have h0 : rem I.1 ⟨k, i⟩ k = ∅ := by
          rw [rem_apply_self]; exact Finset.not_nonempty_iff_eq_empty.1 hne
        rw [ext_of_empty _ h0]
        refine (Finset.sum_eq_zero fun k' _ => Finset.sum_eq_zero fun i' _ => ?_).symm
        rw [ext_of_empty (k := k), smul_zero]
        by_cases hk : k = k'
        · subst hk; rw [rem_apply_self, h0, Finset.erase_empty]
        · rw [rem_apply_of_ne _ hk, h0]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => by rw [key k i hi]]
    exact double_sum_eq_zero I.1 (ext n s) (ext_ne_zero s)
  · exact cellD_apply_not S y (n + 1) _ I hI

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
