import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.PointMatrixPhases

open Formalism.MainNotions.S Formalism.L2.SG.Pf

variable {K : Type} [Field K] {N : ℕ}

def sgLoF (L : Matrix (Fin N) (Fin N) K) : K := ∑ a : Fin N, if h : a.val + 1 < N then L ⟨a.val + 1, h⟩ a else 0

def sgUpF (U : Matrix (Fin N) (Fin N) K) : K := ∑ a : Fin N, if h : a.val + 1 < N then U a ⟨a.val + 1, h⟩ else 0

private lemma mul_apply_subdiag_of_isLoUni {A B : Matrix (Fin N) (Fin N) K} (hA : IsLoUni A) (hB : IsLoUni B) (a : Fin N)
    (h : a.val + 1 < N) : (A * B) ⟨a.val + 1, h⟩ a = A ⟨a.val + 1, h⟩ a + B ⟨a.val + 1, h⟩ a := by
  set b : Fin N := ⟨a.val + 1, h⟩ with hb
  have hab : a ≠ b := by
    intro e; have := congrArg Fin.val e; simp [b] at this
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
  · rw [(hB a a).2 rfl, (hA b b).2 rfl]; ring
  · rintro x ⟨hxa, hxb⟩
    rcases lt_or_gt_of_ne hxa with hx | hx
    · rw [(hB x a).1 hx, mul_zero]
    · have hbx : b < x := by
        have h1 : x.val ≠ a.val + 1 := fun e => hxb (Fin.ext e)
        rw [Fin.lt_iff_val_lt_val] at hx ⊢
        simp only [b]; omega
      rw [(hA b x).1 hbx, zero_mul]

theorem sgLoF_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsLoUni A) (hB : IsLoUni B) :
    sgLoF (A * B) = sgLoF A + sgLoF B := by
  unfold sgLoF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · exact mul_apply_subdiag_of_isLoUni hA hB a h
  · simp

private lemma mul_apply_superdiag_of_isUpUni {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) (a : Fin N)
    (h : a.val + 1 < N) : (A * B) a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩ + B a ⟨a.val + 1, h⟩ := by
  set b : Fin N := ⟨a.val + 1, h⟩ with hb
  have hab : a ≠ b := by
    intro e; have := congrArg Fin.val e; simp [b] at this
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
  · rw [(hA a a).2 rfl, (hB b b).2 rfl]; ring
  · rintro x ⟨hxa, hxb⟩
    rcases lt_or_gt_of_ne hxa with hx | hx
    · rw [(hA a x).1 hx, zero_mul]
    · have hbx : b < x := by
        have h1 : x.val ≠ a.val + 1 := fun e => hxb (Fin.ext e)
        rw [Fin.lt_iff_val_lt_val] at hx ⊢
        simp only [b]; omega
      rw [(hB x b).1 hbx, mul_zero]

theorem sgUpF_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) :
    sgUpF (A * B) = sgUpF A + sgUpF B := by
  unfold sgUpF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · exact mul_apply_superdiag_of_isUpUni hA hB a h
  · simp

def sameBF (bs : List (K × ℕ)) (N a : ℕ) : Prop :=
  a + 1 < N ∧ pσ bs (a + 1) + 1 = pσ bs a ∧ pv bs (a + 1) = pv bs a

private theorem pv_psigma_eq_pv : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    pv bs (pσ bs i) = pv bs i := by
  intro bs
  induction bs with
  | nil => intro i h; simp at h
  | cons b bs ih =>
    intro i h
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · have h1 : s - 1 - i < s := by omega
      simp only [pσ, pv, hi, h1, if_true]
    · have h1 : ¬ s + pσ bs (i - s) < s := by omega
      simp only [pσ, pv, hi, h1, if_false, Nat.add_sub_cancel_left]
      exact ih (i - s) (by omega)

theorem same_phiF (p : Point K N) {a : ℕ} (hs : sameBF p.1 N a) :
    sameBF p.1 N (pσ p.1 (a + 1)) ∧ pσ p.1 (pσ p.1 (a + 1) + 1) = a := by
  have hsum : (p.1.map Prod.snd).sum = N := p.2.2
  unfold sameBF at hs ⊢
  obtain ⟨h1, h2, h3⟩ := hs
  have ha : a < N := by omega
  have hσa := pσ_lt p.1 a (by rw [hsum]; exact ha)
  have hinv1 := pσ_inv p.1 (a + 1) (by rw [hsum]; exact h1)
  have hinv0 := pσ_inv p.1 a (by rw [hsum]; exact ha)
  have hv1 := pv_psigma_eq_pv p.1 (a + 1) (by rw [hsum]; exact h1)
  have hv0 := pv_psigma_eq_pv p.1 a (by rw [hsum]; exact ha)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h2]; exact lt_of_lt_of_eq hσa hsum
  · rw [h2, hinv0, hinv1]
  · rw [h2, hv0, hv1, h3]
  · rw [h2, hinv0]

private theorem pv_ne_zero_of_blocks_ne_zero : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ i, i < (bs.map Prod.snd).sum → pv bs i ≠ 0 := by
  intro bs
  induction bs with
  | nil => intro _ i h; simp at h
  | cons b bs ih =>
    intro hb i h
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h
    simp only [pv]
    split_ifs with hi
    · exact (hb (t, s) (by simp)).1
    · exact ih (fun b hb' => hb b (by simp [hb'])) (i - s) (by omega)

private lemma mul_ptMat_apply_eq (p : Point K N) (A : Matrix (Fin N) (Fin N) K) (i j k : Fin N)
    (hk : k.val = pσ p.1 j.val) : (A * ptMat p) i j = A i k * pv p.1 k.val := by
  have hs : (p.1.map Prod.snd).sum = N := p.2.2
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · have e : ptMat p k j = pv p.1 k.val := by
      show ptEntry p.1 k.val j.val = _
      rw [ptEntry_eq_pv p.1 _ _ (by rw [hs]; exact k.isLt), if_pos]
      rw [hk, pσ_inv p.1 _ (by rw [hs]; exact j.isLt)]
    rw [e]
  · intro c _ hc
    have e : ptMat p c j = 0 := by
      show ptEntry p.1 c.val j.val = _
      rw [ptEntry_eq_pv p.1 _ _ (by rw [hs]; exact c.isLt), if_neg]
      intro e
      apply hc
      apply Fin.ext
      rw [hk, e, pσ_inv p.1 _ (by rw [hs]; exact c.isLt)]
    rw [e, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma ptMat_mul_apply_eq (p : Point K N) (A : Matrix (Fin N) (Fin N) K) (i j k : Fin N)
    (hk : k.val = pσ p.1 i.val) : (ptMat p * A) i j = pv p.1 i.val * A k j := by
  have hs : (p.1.map Prod.snd).sum = N := p.2.2
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · have e : ptMat p i k = pv p.1 i.val := by
      show ptEntry p.1 i.val k.val = _
      rw [ptEntry_eq_pv p.1 _ _ (by rw [hs]; exact i.isLt), if_pos hk]
    rw [e]
  · intro c _ hc
    have e : ptMat p i c = 0 := by
      show ptEntry p.1 i.val c.val = _
      rw [ptEntry_eq_pv p.1 _ _ (by rw [hs]; exact i.isLt), if_neg]
      intro e
      exact hc (Fin.ext (e.trans hk.symm))
    rw [e, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem simple_eqF (p : Point K N) {n m : Matrix (Fin N) (Fin N) K} (hn : IsLoUni n) (hm : IsUpUni m)
    (h : n * ptMat p = ptMat p * m) : sgLoF n = sgUpF m := by
  have hs : (p.1.map Prod.snd).sum = N := p.2.2
  have hbs := p.2.1
  have hlt : ∀ i, i < N → pσ p.1 i < N := fun i hi => by
    have := pσ_lt p.1 i (by rw [hs]; exact hi); rwa [hs] at this
  have hinv : ∀ i, i < N → pσ p.1 (pσ p.1 i) = i := fun i hi => pσ_inv p.1 i (by rw [hs]; exact hi)
  have hv : ∀ i, i < N → pv p.1 i ≠ 0 := fun i hi => pv_ne_zero_of_blocks_ne_zero p.1 hbs i (by rw [hs]; exact hi)
  have key : ∀ (i j k l : Fin N), k.val = pσ p.1 j.val → l.val = pσ p.1 i.val →
      n i k * pv p.1 k.val = pv p.1 i.val * m l j := by
    intro i j k l hk hl
    have := congrFun (congrFun h i) j
    rwa [mul_ptMat_apply_eq p n i j k hk, ptMat_mul_apply_eq p m i j l hl] at this
  have hlo : ∀ a : Fin N, (if h : a.val + 1 < N then n ⟨a.val + 1, h⟩ a else 0) =
      if hS : sameBF p.1 N a.val then
        m ⟨pσ p.1 (a.val + 1), hlt _ hS.1⟩ ⟨pσ p.1 (a.val + 1) + 1, by rw [hS.2.1]; exact hlt _ a.isLt⟩
      else 0 := by
    intro a
    by_cases ha : a.val + 1 < N
    · rw [dif_pos ha]
      have K1 := key ⟨a.val + 1, ha⟩ ⟨pσ p.1 a.val, hlt _ a.isLt⟩ a ⟨pσ p.1 (a.val + 1), hlt _ ha⟩
        (hinv _ a.isLt).symm rfl
      split_ifs with hS
      · obtain ⟨_, h2, h3⟩ := hS
        have e : (⟨pσ p.1 a.val, hlt _ a.isLt⟩ : Fin N) =
            ⟨pσ p.1 (a.val + 1) + 1, by rw [h2]; exact hlt _ a.isLt⟩ := Fin.ext h2.symm
        have h3' : pv p.1 (Fin.val (⟨a.val + 1, ha⟩ : Fin N)) = pv p.1 a.val := h3
        rw [e, h3'] at K1
        exact mul_right_cancel₀ (hv _ a.isLt) (K1.trans (mul_comm _ _))
      · rcases pσ_nb p.1 hbs a.val (by rw [hs]; exact ha) with hsame | hgt
        · exact absurd ⟨ha, hsame.1, hsame.2⟩ hS
        · have e : m ⟨pσ p.1 (a.val + 1), hlt _ ha⟩ ⟨pσ p.1 a.val, hlt _ a.isLt⟩ = 0 :=
            (hm _ _).1 (by rw [Fin.lt_iff_val_lt_val]; exact hgt)
          rw [e, mul_zero] at K1
          exact (mul_eq_zero.1 K1).resolve_right (hv _ a.isLt)
    · rw [dif_neg ha, dif_neg (fun hS => ha hS.1)]
  have hup : ∀ b : Fin N, (if h : b.val + 1 < N then m b ⟨b.val + 1, h⟩ else 0) =
      if hS : sameBF p.1 N b.val then m b ⟨b.val + 1, hS.1⟩ else 0 := by
    intro b
    by_cases hb : b.val + 1 < N
    · rw [dif_pos hb]
      split_ifs with hS
      · rfl
      · rcases pσ_nb p.1 hbs b.val (by rw [hs]; exact hb) with hsame | hgt
        · exact absurd ⟨hb, hsame.1, hsame.2⟩ hS
        · have K1 := key ⟨pσ p.1 b.val, hlt _ b.isLt⟩ ⟨b.val + 1, hb⟩ ⟨pσ p.1 (b.val + 1), hlt _ hb⟩ b
            rfl (hinv _ b.isLt).symm
          have e : n ⟨pσ p.1 b.val, hlt _ b.isLt⟩ ⟨pσ p.1 (b.val + 1), hlt _ hb⟩ = 0 :=
            (hn _ _).1 (by rw [Fin.lt_iff_val_lt_val]; exact hgt)
          rw [e, zero_mul] at K1
          exact (mul_eq_zero.1 K1.symm).resolve_left (hv _ (hlt _ b.isLt))
    · rw [dif_neg hb, dif_neg (fun hS => hb hS.1)]
  unfold sgLoF sgUpF
  rw [Finset.sum_congr rfl (fun a _ => hlo a), Finset.sum_congr rfl (fun b _ => hup b)]
  set fe : Fin N → Fin N := fun a =>
    if hS : sameBF p.1 N a.val then ⟨pσ p.1 (a.val + 1), hlt _ hS.1⟩ else a with hfe
  have hinvol : Function.Involutive fe := by
    intro a
    by_cases hS : sameBF p.1 N a.val
    · have h2 := same_phiF p hS
      apply Fin.ext
      simp [hfe, hS, h2.1, h2.2]
    · simp [hfe, hS]
  refine Fintype.sum_equiv (hinvol.toPerm _) _ _ (fun a => ?_)
  by_cases hS : sameBF p.1 N a.val
  · have h2 := same_phiF p hS
    simp [hfe, hS, h2.1]
  · simp [hfe, hS]

theorem decompSimpleF (p : Point K N) {L U L' U' : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) (hU : IsUpUni U)
    (hL' : IsLoUni L') (hU' : IsUpUni U') (e : L * ptMat p * U = L' * ptMat p * U') :
    sgLoF L + sgUpF U = sgLoF L' + sgUpF U' := by
  obtain ⟨hn, hm, hnm, hL1, hU1⟩ := cell_move hL hU hL' hU' e
  have hs := simple_eqF p hn hm hnm
  have h1 : sgLoF L = sgLoF L' + sgLoF (L'⁻¹ * L) := by rw [← sgLoF_mul hL' hn, hL1]
  have h2 : sgUpF U' = sgUpF (U' * U⁻¹) + sgUpF U := by rw [← sgUpF_mul hm hU, hU1]
  rw [h1, h2, hs]; ring

def mapPt {K' : Type} [Field K'] (f : K →+* K') (p : Point K N) : Point K' N :=
  ⟨p.1.map (fun b => (f b.1, b.2)), by
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      exact ⟨(map_ne_zero f).2 (p.2.1 c hc).1, (p.2.1 c hc).2⟩
    · rw [List.map_map]; exact p.2.2⟩

theorem ptEntry_map {K' : Type} [Field K'] (f : K →+* K') :
    ∀ (bs : List (K × ℕ)) (i j : ℕ), ptEntry (bs.map (fun b => (f b.1, b.2))) i j = f (ptEntry bs i j)
  | [], _, _ => by simp [ptEntry]
  | (t, s) :: bs, i, j => by
    simp only [List.map_cons, ptEntry]
    split_ifs <;> simp [ptEntry_map f bs]

theorem ptMat_mapPt {K' : Type} [Field K'] (f : K →+* K') (p : Point K N) : ptMat (mapPt f p) = (ptMat p).map f := by
  ext a b
  exact ptEntry_map f p.1 a.val b.val

end Formalism.L2.SG.Pf.PointMatrixPhases
