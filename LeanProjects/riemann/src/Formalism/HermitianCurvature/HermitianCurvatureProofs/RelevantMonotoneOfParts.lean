import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x4

variable {m : ℕ}

def Cond (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Prop :=
  ∀ a b : Fin m, a < b → w b < w a →
    ((b.val = a.val + 1 ↔ (w a).val = (w b).val + 1) ∧ (b.val = a.val + 1 → d a = d b))

def IsCut (w : Equiv.Perm (Fin m)) (c : Fin m) : Prop := ∀ x y : Fin m, x ≤ c → c < y → w x < w y

lemma cut_of_ascent (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m)
    (ha : a.val + 1 < m) (hasc : w a < w ⟨a.val + 1, ha⟩) : IsCut w a := by
  have key : ∀ n : ℕ, ∀ x y : Fin m, x ≤ a → a < y → w y < w x → (w x).val - (w y).val = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hx hy hxy hn
      have hxy' : x < y := lt_of_le_of_lt hx hy
      by_cases h1 : (w x).val = (w y).val + 1
      · have := ((hC x y hxy' hxy).1).mpr h1
        have hxa : x = a := by
          apply Fin.ext; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        have hya : y = ⟨a.val + 1, ha⟩ := by
          apply Fin.ext; simp only; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        rw [hxa, hya] at hxy
        exact absurd hasc (not_lt.mpr (le_of_lt hxy))
      · have hlt : (w y).val + 1 < (w x).val := by
          rw [Fin.lt_def] at hxy; omega
        set v : Fin m := ⟨(w y).val + 1, by omega⟩ with hv
        set z := w.symm v with hz
        have hwz : w z = v := by rw [hz, Equiv.apply_symm_apply]
        by_cases hza : z ≤ a
        · apply ih ((w z).val - (w y).val) (by rw [hwz]; simp only [hv]; omega) z y hza hy
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
        · push_neg at hza
          apply ih ((w x).val - (w z).val) (by rw [hwz]; simp only [hv]; omega) x z hx hza
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
  intro x y hx hy
  by_contra hcon
  push_neg at hcon
  have hne : w y ≠ w x := fun e => (ne_of_lt (lt_of_le_of_lt hx hy)) (w.injective e).symm
  exact key _ x y hx hy (lt_of_le_of_ne hcon hne) rfl

lemma cut_preserves (w : Equiv.Perm (Fin m)) (c : Fin m) (hc : IsCut w c) (x : Fin m) :
    x ≤ c ↔ w x ≤ c := by
  set S := Finset.univ.filter (fun x : Fin m => x ≤ c) with hS
  set T := Finset.univ.filter (fun x : Fin m => w x ≤ c) with hT
  have hTS : T = S.map w.symm.toEmbedding := by
    ext x; simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨w x, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hcard : T.card = S.card := by rw [hTS, Finset.card_map]
  have hsub : S ⊆ T := by
    intro x hx
    by_contra hxT
    have hTnot : ¬ T ⊆ S := by
      intro hTS'
      have := Finset.eq_of_subset_of_card_le hTS' (le_of_eq hcard.symm)
      rw [this] at hxT; exact hxT hx
    obtain ⟨y, hyT, hyS⟩ := Finset.not_subset.mp hTnot
    simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx hxT hyT hyS
    have := hc x y hx hyS
    exact absurd (lt_of_le_of_lt hyT hxT) (not_lt.mpr (le_of_lt this))
  have hEq : S = T := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
  have := congrArg (fun F => x ∈ F) hEq
  simpa [hS, hT] using this

open Classical in

noncomputable def blk (w : Equiv.Perm (Fin m)) (a : Fin m) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c)).card

lemma blk_mono (w : Equiv.Perm (Fin m)) : Monotone (blk w) := by
  intro a b hab
  unfold blk
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact ⟨lt_of_lt_of_le hc.1 hab, hc.2⟩

lemma blk_w (w : Equiv.Perm (Fin m)) (a : Fin m) : blk w (w a) = blk w a := by
  unfold blk
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push_neg at h
    have := (cut_preserves w c h2 a).mp h
    exact absurd h1 (not_lt.mpr this)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push_neg at h
    have := (cut_preserves w c h2 a).mpr h
    exact absurd h1 (not_lt.mpr this)

lemma no_cut_between (w : Equiv.Perm (Fin m)) (a b j : Fin m) (hab : blk w a = blk w b)
    (hj1 : a ≤ j) (hj2 : j < b) : ¬ IsCut w j := by
  intro hcut
  classical
  have hss : Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c) ⊂
      Finset.univ.filter (fun c : Fin m => c < b ∧ IsCut w c) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj2, hcut⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; exact absurd h (not_lt.mpr hj1)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨lt_trans hc.1 (lt_of_le_of_lt hj1 hj2), hc.2⟩
  have := Finset.card_lt_card hss
  unfold blk at hab
  rw [hab] at this
  exact lt_irrefl _ this

lemma desc_in_block (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a b : Fin m)
    (hab : blk w a = blk w b) (j : Fin m) (hj1 : a ≤ j) (hj2 : j.val + 1 ≤ b.val) :
    ∃ h : j.val + 1 < m, w ⟨j.val + 1, h⟩ < w j := by
  have h : j.val + 1 < m := lt_of_le_of_lt hj2 b.isLt
  refine ⟨h, ?_⟩
  have hne : w ⟨j.val + 1, h⟩ ≠ w j := fun e => by
    have := congrArg Fin.val (w.injective e); simp at this
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact h1
  · exfalso
    exact no_cut_between w a b j hab hj1 (by rw [Fin.lt_def]; omega) (cut_of_ascent w d hC j h h1)

lemma chain (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m) :
    ∀ n : ℕ, ∀ b : Fin m, b.val = a.val + n + 1 → blk w a = blk w b → w b < w a ∧ d a = d b := by
  intro n
  induction n with
  | zero =>
    intro b hb hab
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab a le_rfl (by omega)
    have hbe : b = ⟨a.val + 1, h⟩ := Fin.ext (by simp only; omega)
    subst hbe
    refine ⟨hd, ?_⟩
    exact (hC a _ (by rw [Fin.lt_def]; simp) hd).2 rfl
  | succ n ih =>
    intro b hb hab
    set j : Fin m := ⟨a.val + n + 1, by omega⟩ with hj
    have hmono := blk_mono w
    have haj : blk w a = blk w j := by
      apply le_antisymm (hmono (by rw [Fin.le_def]; simp only [hj]; omega))
      rw [hab]; exact hmono (by rw [Fin.le_def]; simp only [hj]; omega)
    obtain ⟨h1, h2⟩ := ih j rfl haj
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab j (by rw [Fin.le_def]; simp only [hj]; omega)
      (by simp only [hj]; omega)
    have hbe : b = ⟨j.val + 1, h⟩ := Fin.ext (by simp only [hj]; omega)
    rw [hbe] at hab ⊢
    refine ⟨lt_trans hd h1, ?_⟩
    rw [h2]
    exact (hC j _ (by rw [Fin.lt_def]; simp) hd).2 rfl

end C2x4

open C2x4

theorem relevant_criterion : C2.RelevantCrit := by
  intro m w d
  constructor
  · intro hC
    refine ⟨blk w, blk_mono w, blk_w w, ?_, ?_⟩
    · intro a b hab hlt
      exact (chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at hlt; omega) hab).1
    · intro a b hab
      rcases lt_trichotomy a b with h | rfl | h
      · exact (chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at h; omega) hab).2
      · rfl
      · exact ((chain w d hC b (a.val - b.val - 1) a (by rw [Fin.lt_def] at h; omega) hab.symm).2).symm
  · rintro ⟨bl, hmono, hw, hrev, hd⟩ a b hab hwab
    have hsame : bl a = bl b := by
      apply le_antisymm (hmono (le_of_lt hab))
      rw [← hw a, ← hw b]; exact hmono (le_of_lt hwab)

    have hin : ∀ c : Fin m, a ≤ c → c ≤ b → bl c = bl a := by
      intro c h1 h2
      apply le_antisymm
      · rw [hsame]; exact hmono h2
      · exact hmono h1
    have hinv : ∀ c : Fin m, w b ≤ c → c ≤ w a → bl (w.symm c) = bl a := by
      intro c h1 h2
      have : bl c = bl a := by
        apply le_antisymm
        · rw [← hw a]; exact hmono h2
        · rw [hsame, ← hw b]; exact hmono h1
      rw [← hw (w.symm c), Equiv.apply_symm_apply, this]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => hd a b hsame⟩
    ·
      by_contra hne
      have hlt : (w b).val + 1 < (w a).val := by rw [Fin.lt_def] at hwab; omega
      set c : Fin m := ⟨(w b).val + 1, by omega⟩ with hc
      have hcb : bl (w.symm c) = bl a :=
        hinv c (by rw [Fin.le_def]; simp only [hc]; omega) (by rw [Fin.le_def]; simp only [hc]; omega)
      have hwc : w (w.symm c) = c := Equiv.apply_symm_apply w c

      have h1 : a < w.symm c := by
        rcases lt_trichotomy (w.symm c) a with h' | h' | h'
        · have := hrev (w.symm c) a (hcb.trans rfl) h'
          rw [hwc] at this; rw [Fin.lt_def] at this; simp only [hc] at this; omega
        · rw [← h', hwc] at hlt; simp only [hc] at hlt; omega
        · exact h'
      have h2 : w.symm c < b := by
        rcases lt_trichotomy (w.symm c) b with h' | h' | h'
        · exact h'
        · rw [h', hc] at hwc; have := congrArg Fin.val hwc; simp at this
        · have := hrev b (w.symm c) (hsame.symm.trans hcb.symm) h'
          rw [hwc] at this; rw [Fin.lt_def] at this; simp only [hc] at this; omega
      rw [Fin.lt_def] at h1 h2; omega
    ·
      by_contra hne
      have hlt : a.val + 1 < b.val := by rw [Fin.lt_def] at hab; omega
      set c : Fin m := ⟨a.val + 1, by omega⟩ with hc
      have hca : bl c = bl a := hin c (by rw [Fin.le_def]; simp only [hc]; omega)
        (by rw [Fin.le_def]; simp only [hc]; omega)
      have e1 := hrev a c hca.symm (by rw [Fin.lt_def]; simp only [hc]; omega)
      have e2 := hrev c b (hca.trans hsame) (by rw [Fin.lt_def]; simp only [hc]; omega)
      rw [Fin.lt_def] at e1 e2; omega

lemma c2x4_simpleLow_double {m : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleLow l = ∑ p : Fin m, ∑ q : Fin m, if p.val = q.val + 1 then l p q else 0 := by
  unfold C2.simpleLow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨q.val + 1, h⟩]
    · simp
    · intro p _ hp; rw [if_neg]; intro e; exact hp (Fin.ext e)
    · simp
  · apply (Finset.sum_eq_zero (fun p _ => ?_)).symm
    rw [if_neg]; intro e; have := p.isLt; omega

lemma c2x4_simpleUp_double {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleUp u = ∑ a : Fin m, ∑ b : Fin m, if b.val = a.val + 1 then u a b else 0 := by
  unfold C2.simpleUp
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val + 1, h⟩]
    · simp
    · intro p _ hp; rw [if_neg]; intro e; exact hp (Fin.ext e)
    · simp
  · apply (Finset.sum_eq_zero (fun p _ => ?_)).symm
    rw [if_neg]; intro e; have := p.isLt; omega

lemma c2x4_ut_inv_super' {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a b : Fin m)
    (hb : b.val = a.val + 1) : u⁻¹ a b = -u a b := by
  obtain ⟨bv, hbv⟩ := b
  simp only at hb
  subst hb
  exact C2x2.ut_inv_super hu a hbv

lemma c2x4_stab_sum_zero {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (hC : Cond w d) (l u' : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (hu : u' ∈ C2.UTset m)
    (he : l * C2.monoP w d * u' = C2.monoP w d) : C2.simpleLow l + C2.simpleUp u' = 0 := by
  have hPu := C2x2.isUnit_det_monomialMatrix w d hd
  have hinv : (C2.monoP w d)⁻¹ * l * C2.monoP w d = u'⁻¹ := by
    calc (C2.monoP w d)⁻¹ * l * C2.monoP w d
        = (C2.monoP w d)⁻¹ * l * C2.monoP w d * (u' * u'⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ (C2x2.ut_unit hu), Matrix.mul_one]
      _ = (C2.monoP w d)⁻¹ * (l * C2.monoP w d * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
  have hent : ∀ a b : Fin m, l (w a) (w b) = d a * u'⁻¹ a b / d b := by
    intro a b
    have := congrFun (congrFun hinv a) b
    rw [C2x2.monomialMatrix_conj_apply w d hd] at this
    rw [← this]; field_simp [hd a, hd b]
  have hui := C2x2.ut_inv hu
  rw [c2x4_simpleLow_double, c2x4_simpleUp_double]
  rw [← Equiv.sum_comp w]
  simp_rw [← Equiv.sum_comp w (fun q => if (w _).val = q.val + 1 then l (w _) q else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  by_cases h1 : b.val = a.val + 1
  · have hab : a < b := by rw [Fin.lt_def]; omega
    have hsup := C2x2.ut_inv_super hu a (by omega)
    have hbe : b = ⟨a.val + 1, by omega⟩ := Fin.ext h1
    by_cases h2 : (w a).val = (w b).val + 1
    · have hwab : w b < w a := by rw [Fin.lt_def]; omega
      have hda := (hC a b hab hwab).2 h1
      rw [if_pos h2, if_pos h1, hent, hda]
      have e : d b * u'⁻¹ a b / d b = u'⁻¹ a b := by field_simp [hd b]
      rw [e, c2x4_ut_inv_super' hu a b h1]; ring
    · rw [if_neg h2, if_pos h1, zero_add]
      have hwab : w a < w b := by
        rcases lt_or_gt_of_ne (fun e : w a = w b => (ne_of_lt hab) (w.injective e)) with h | h
        · exact h
        · exact absurd ((hC a b hab h).1.mp h1) h2
      have hz := hl.1 (w a) (w b) hwab
      rw [hent] at hz
      have : u'⁻¹ a b = 0 := by
        rcases mul_eq_zero.mp (div_eq_zero_iff.mp hz |>.resolve_right (hd b)) with h | h
        · exact absurd h (hd a)
        · exact h
      rw [c2x4_ut_inv_super' hu a b h1, neg_eq_zero] at this
      exact this
  · rw [if_neg h1, add_zero]
    by_cases h2 : (w a).val = (w b).val + 1
    · rw [if_pos h2, hent]
      rcases lt_trichotomy a b with h | rfl | h
      · have hwab : w b < w a := by rw [Fin.lt_def]; omega
        exact absurd ((hC a b h hwab).1.mpr h2) h1
      · omega
      · rw [hui.1 a b h]; simp
    · rw [if_neg h2]

theorem relevant_monotone : C2.RelevantMono := by
  intro m w d c hd hc
  rw [← relevant_criterion m w d]
  constructor
  · intro hall a b hab hwab
    rw [← relevant_trivial_case m w d c hd hc a b hab hwab]
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := relevant_pair_criterion m w d hd a b hab hwab x
    rw [← h4]
    exact hall _ h1 _ h2 h3
  · intro hC l hl u' hu he
    rw [c2x4_stab_sum_zero w d hd hC l u' hl hu he]
    simp [C2.psiC]

theorem relevant_monotone_of_parts_alt : C2.RelevantMonoOfParts := fun _ _ _ _ => relevant_monotone

end Formalism.FourierDecayAlt.P
