import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.TsumTruncatedShiftLe
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.St

variable {D : D7} {L : SizeData₂ D}

theorem bs_add (X : Inst D L) (h u : HH D) (i : ℕ) : X.bs h (u + i • h) = X.bs h u := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem bs_idem (X : Inst D L) (h t : HH D) : X.bs h (X.bs h t) = X.bs h t := by
  obtain ⟨i, hi⟩ := X.bs_orb h t
  have := bs_add X h (X.bs h t) i
  rw [hi] at this
  exact this.symm

theorem not_singular_of_central {p : ℕ} (hc : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro h
  have h2 : PrimeClass.inertClass = PrimeClass.signal := hc.symm.trans h
  cases h2

theorem frobenius_step_large_order {p : ℕ} (hc : IsResidueClassZero D p) : stepP D p = hP D p := by
  unfold stepP
  rw [if_neg (not_singular_of_central hc)]

theorem partner_count_of_central {p : ℕ} (hc : IsResidueClassZero D p) : nP D p = addOrderOf (hP D p) := by
  unfold nP
  rw [if_neg (not_singular_of_central hc)]

def phi (D : D7) (p : ℕ) (t0 : HH D) (i : Fin (addOrderOf (hP D p))) : HH D := t0 + (i : ℕ) • hP D p

theorem phi_inj (p : ℕ) (t0 : HH D) : Function.Injective (phi D p t0) := by
  intro i j hij
  have h1 : (i : ℕ) • hP D p = (j : ℕ) • hP D p := add_left_cancel hij
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf (Set.mem_Iio.2 i.2) (Set.mem_Iio.2 j.2) h1)

theorem phi_posAdd (p : ℕ) (t0 : HH D) (i : Fin (addOrderOf (hP D p))) (e : ℕ) :
    phi D p t0 (posAdd i e) = phi D p t0 i + e • hP D p := by
  unfold phi posAdd
  simp only
  rw [mod_addOrderOf_nsmul, add_nsmul, add_assoc]

theorem bs_phi (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0)
    (i : Fin (addOrderOf (hP D p))) : X.bs (stepP D p) (phi D p t0 i) = t0 := by
  rw [frobenius_step_large_order hc] at h0 ⊢
  unfold phi
  rw [bs_add, h0]

theorem reps_fix (X : Inst D L) {p : ℕ} {t0 : HH D} (h : t0 ∈ reps X p) : X.bs (stepP D p) t0 = t0 := by
  unfold reps at h
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h
  exact bs_idem X _ t

theorem topsOn_eq_image (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) :
    topsOn X p t0 = (topsPos D p t0).image (phi D p t0) := by
  classical
  ext t
  unfold topsOn topsPos
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht, hb⟩
    obtain ⟨i, hi⟩ := X.bs_orb (stepP D p) t
    rw [hb, frobenius_step_large_order hc] at hi
    have hpos : 0 < addOrderOf (hP D p) := addOrderOf_pos _
    refine ⟨⟨i % addOrderOf (hP D p), Nat.mod_lt _ hpos⟩, ?_, ?_⟩
    · simp only
      rw [mod_addOrderOf_nsmul, hi]
      exact ht
    · unfold phi
      simp only
      rw [mod_addOrderOf_nsmul, hi]
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, bs_phi X hc h0 i⟩

theorem sum_topsOn (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0)
    (F : HH D → ℝ) : ∑ s ∈ topsOn X p t0, F s = ∑ i ∈ topsPos D p t0, F (phi D p t0 i) := by
  classical
  rw [topsOn_eq_image X hc h0, Finset.sum_image (fun x _ y _ h => phi_inj p t0 h)]

theorem Nv_eq_card (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) :
    Nv X p t0 = (topsPos D p t0).card := by
  classical
  unfold Nv
  rw [topsOn_eq_image X hc h0, Finset.card_image_of_injective _ (phi_inj p t0)]

theorem isV_phi (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0)
    (i : Fin (addOrderOf (hP D p))) : IsV X p (phi D p t0 i) ↔ IsTypeV i := by
  unfold IsV IsTypeV
  rw [bs_phi X hc h0, partner_count_of_central hc]
  constructor
  · rintro ⟨i', hi', hev, hh⟩
    have : (⟨i', hi'⟩ : Fin (addOrderOf (hP D p))) = i := phi_inj p t0 hh
    rw [← this]
    exact hev
  · intro hev
    exact ⟨i, i.2, hev, rfl⟩

theorem dMinus_spec {n' : ℕ} (TT : Finset (Fin n')) (y : Fin n') (hd : dMinus TT y ≠ 0) :
    0 < dMinus TT y ∧ dMinus TT y ≤ n' ∧ posAdd y (n' - dMinus TT y) ∈ TT ∧
      IsTypeV (posAdd y (n' - dMinus TT y)) := by
  classical
  unfold dMinus at hd ⊢
  split_ifs at hd ⊢ with h
  · exact Nat.find_spec h
  · exact absurd rfl hd

theorem posAdd_back {n' : ℕ} (y : Fin n') (d : ℕ) (hd : d ≤ n') : posAdd (posAdd y (n' - d)) d = y := by
  apply Fin.ext
  unfold posAdd
  simp only
  rw [Nat.mod_add_mod, show y.val + (n' - d) + d = y.val + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt y.2]

theorem dMinus_odd {n' : ℕ} (hn : Even n') (TT : Finset (Fin n')) (y : Fin n') (hy : ¬ IsTypeV y)
    (hd : dMinus TT y ≠ 0) : Odd (dMinus TT y) := by
  obtain ⟨h1, h2, -, h4⟩ := dMinus_spec TT y hd
  unfold IsTypeV at h4 hy
  unfold posAdd at h4
  simp only at h4
  obtain ⟨q, hq⟩ := hn
  have h2n : 2 ∣ n' := ⟨q, by omega⟩
  rw [Nat.even_iff, Nat.mod_mod_of_dvd _ h2n] at h4
  rw [Nat.even_iff] at hy
  rw [Nat.odd_iff]
  omega

open Classical in
theorem kink {n' : ℕ} (hn : Even n') (TT : Finset (Fin n')) (q : ℝ) (hq : 2 ≤ q) (a W : Fin n' → ℝ)
    (ha : ∀ x ∈ TT, 0 ≤ a x) (hW : ∀ x, 0 ≤ W x) :
    ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else min (W y) (a (posAdd y (n' - dMinus TT y)) / q ^ dMinus TT y)) ≤
    ∑ x ∈ TT.filter (fun x => IsTypeV x),
      ∑' e : ℕ, (if Odd e then min (a x / q ^ e) (W (posAdd x e)) else 0) := by
  set S := (TT.filter (fun y => ¬ IsTypeV y)).filter (fun y => dMinus TT y ≠ 0) with hS
  set xm : Fin n' → Fin n' := fun y => posAdd y (n' - dMinus TT y) with hxm
  set g : Fin n' → ℕ → ℝ := fun x e => min (a x / q ^ e) (W (posAdd x e)) with hg
  have h1 : ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else min (W y) (a (xm y) / q ^ dMinus TT y)) =
      ∑ y ∈ S, g (xm y) (dMinus TT y) := by
    symm
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hd : dMinus TT y = 0
    · rw [if_pos hd, if_neg (not_not.2 hd)]
    · rw [if_neg hd, if_pos hd]
      simp only [hg, hxm]
      rw [posAdd_back y _ (dMinus_spec TT y hd).2.1, min_comm]
  rw [h1]
  have hmaps : ∀ y ∈ S, xm y ∈ TT.filter (fun x => IsTypeV x) := by
    intro y hy
    have hd := (Finset.mem_filter.1 hy).2
    obtain ⟨_, _, h3, h4⟩ := dMinus_spec TT y hd
    exact Finset.mem_filter.2 ⟨h3, h4⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro x hx
  have hxT := (Finset.mem_filter.1 hx).1
  set Fb := S.filter (fun y => xm y = x) with hFb
  have hinj : ∀ y ∈ Fb, ∀ y' ∈ Fb, dMinus TT y = dMinus TT y' → y = y' := by
    intro y hy y' hy' hdd
    have e1 : xm y = x := (Finset.mem_filter.1 hy).2
    have e2 : xm y' = x := (Finset.mem_filter.1 hy').2
    have d1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
    have d2 := (Finset.mem_filter.1 (Finset.mem_filter.1 hy').1).2
    have b1 : posAdd (xm y) (dMinus TT y) = y := posAdd_back y _ (dMinus_spec TT y d1).2.1
    have b2 : posAdd (xm y') (dMinus TT y') = y' := posAdd_back y' _ (dMinus_spec TT y' d2).2.1
    calc y = posAdd (xm y) (dMinus TT y) := b1.symm
      _ = posAdd (xm y') (dMinus TT y') := by rw [e1, e2, hdd]
      _ = y' := b2
  have h2 : ∑ y ∈ Fb, g (xm y) (dMinus TT y) =
      ∑ e ∈ Fb.image (dMinus TT), (if Odd e then g x e else 0) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro y hy
    have e1 : xm y = x := (Finset.mem_filter.1 hy).2
    have hyS := (Finset.mem_filter.1 hy).1
    have d1 := (Finset.mem_filter.1 hyS).2
    have o1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hyS).1).2
    rw [if_pos (dMinus_odd hn TT y o1 d1), e1]
  rw [h2]
  have hg0 : ∀ e, 0 ≤ g x e := fun e => le_min (div_nonneg (ha x hxT) (by positivity)) (hW _)
  apply Summable.sum_le_tsum
  · intro e _
    split_ifs
    · exact hg0 e
    · exact le_rfl
  · exact summable_if_of_le q (a x) hq _ _ hg0 (fun e => min_le_left _ _)

theorem base (P : ParameterChoice' D L) : 500 ≤ L.sc.w'' D.R.n ∧ cG L ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧
    0 ≤ cG L ∧ L.Sc ≤ cG L := by
  obtain ⟨hk, hN, hSc⟩ := Nm_le_Sc P
  have hkS := P.kS_le
  obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n D.R.ord_pos
  have hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk (by linarith)
  unfold cG
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem fill_ge_one (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) (j : ℕ)
    (z : Bool × HH D) : 1 ≤ fill X b j z := by
  obtain ⟨h500, _, hwb, _, _⟩ := base P
  have hx := sc_x_pos L.sc
  unfold fill
  by_cases ht : z.1 = false ∧ z.2 ∈ D.host.TT
  · rw [if_pos ht]
    have h1 := (X.off_top j z ht).1
    have h2 := (hW z.2 ht.2).2.2
    have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx.le
    linarith
  · rw [if_neg ht]
    by_cases hth : IsThickPl D z
    · have := (X.off_thick j z hth).1
      have := sc_one_le_b L.sc
      linarith
    · have := (X.off_thin j z ⟨ht, hth⟩).1
      linarith

theorem kaJ_nonneg (D : D7) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : 0 ≤ kaJ D j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have h : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by positivity)
  unfold kaJ
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  linarith

theorem a_bounds (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) {s : HH D} (hs : s ∈ D.host.TT) :
    2 * cG L ≤ (a s : ℝ) ∧ (a s : ℝ) ≤ 2 * L.sc.a ∧ L.sc.a ≤ (a s : ℝ) := by
  obtain ⟨h500, hc, hwb, _, _⟩ := base P
  obtain ⟨hk, _, _⟩ := Nm_le_Sc P
  obtain ⟨h1, h2, _⟩ := hW s hs
  have hab := two_b'_le_a L.sc
  have ha := sc_one_lt_a L.sc
  have h4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a := by
    apply div_le_self (by linarith)
    have : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
    nlinarith
  refine ⟨by linarith, by linarith, h1⟩

def Mn (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  ∑' e : ℕ, if Odd e then min ((a s : ℝ) / (p : ℝ) ^ e) (fill X b j (partner D p s e)) else 0

theorem ask_add_Mn (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime)
    (j : ℕ) {s : HH D} (hs : s ∈ D.host.TT) : askP X a b p j s + Mn X a b p j s = gam p * (a s : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨h1, _, _⟩ := a_bounds P hW hs
  obtain ⟨_, _, _, hc, _⟩ := base P
  unfold askP Mn gam
  exact tsum_pos_add_min (p : ℝ) (a s) hp2 (by linarith) (fun e => fill X b j (partner D p s e))
    (fun e => by have := fill_ge_one X P hW j (partner D p s e); linarith) (fun e => Odd e) (fun e => Iff.rfl)

theorem Mn_nonneg (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ}
    (j : ℕ) {s : HH D} (hs : s ∈ D.host.TT) : 0 ≤ Mn X a b p j s := by
  obtain ⟨h1, _, _⟩ := a_bounds P hW hs
  obtain ⟨_, _, _, hc, _⟩ := base P
  unfold Mn
  apply tsum_nonneg
  intro e
  split_ifs
  · exact le_min (div_nonneg (by linarith) (by positivity))
      (by have := fill_ge_one X P hW j (partner D p s e); linarith)
  · exact le_rfl

theorem odd_top (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime)
    {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT) :
    askP X a b p j s - 3 * cG L * Real.logb p (2 * L.sc.a) ≤ gam p * al L a s -
      ∑' e : ℕ, (if Odd e then min (al L a s / (p : ℝ) ^ e) (capU X b p j s e) else 0) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨h1, h2, _⟩ := a_bounds P hW hs
  obtain ⟨_, _, _, hc, hSc⟩ := base P
  have ha := sc_one_lt_a L.sc
  have hk0 := kaJ_nonneg D j hj
  have hk1 := kaJ_le P j hj
  have hcap0 : ∀ e, 0 ≤ capU X b p j s e := by
    intro e
    have := fill_ge_one X P hW j (partner D p s e)
    unfold capU fillG
    linarith
  have hcap1 : ∀ e, capU X b p j s e ≤ fill X b j (partner D p s e) + cG L := by
    intro e
    unfold capU fillG
    linarith
  have e1 := tsum_pos_add_min (p : ℝ) (al L a s) hp2 (by unfold al; linarith) (fun e => capU X b p j s e) hcap0
    (fun e => Odd e) (fun e => Iff.rfl)
  have e2 := tsum_truncated_shift_le (p : ℝ) (a s) (cG L) (2 * L.sc.a) hp2 hc h1 h2 (by linarith)
    (fun e => fill X b j (partner D p s e)) (fun e => capU X b p j s e)
    (fun e => fill_ge_one X P hW j _) hcap0 hcap1 (fun e => Odd e) (fun e h => h)
  unfold askP gam
  unfold al at e1 ⊢
  linarith

theorem gam_bounds {p : ℕ} (hp : p.Prime) : 0 ≤ gam p ∧ gam p ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  unfold gam
  refine ⟨div_nonneg (by linarith) hd.le, ?_⟩
  rw [div_le_one hd]
  nlinarith

open Classical in

theorem gU_lower (X : Inst D L) (K : Consts) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ}
    (hp : p.Prime) (hlg : 1 ≤ Real.logb p (2 * L.sc.a)) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    (∑ s ∈ topsOn X p t0, askP X a b p j s) +
      (∑ s ∈ (topsOn X p t0).filter (fun s => IsV X p s), Mn X a b p j s) -
      (Nv X p t0 : ℝ) * (3 * cG L * Real.logb p (2 * L.sc.a)) ≤ gU X K a b p j t0 + dl X K p t0 := by
  unfold gU Nv
  set T := topsOn X p t0 with hT
  set lgc := 3 * cG L * Real.logb p (2 * L.sc.a) with hlgc
  have hTT : ∀ s ∈ T, s ∈ D.host.TT := fun s hs => (Finset.mem_filter.1 hs).1
  obtain ⟨_, _, _, hc, _⟩ := base P
  obtain ⟨hg0, hg1⟩ := gam_bounds hp
  have hcl : cG L ≤ cG L * Real.logb p (2 * L.sc.a) := le_mul_of_one_le_right hc hlg
  have hgc : gam p * (2 * cG L) ≤ lgc := by
    have : gam p * (2 * cG L) ≤ 1 * (2 * cG L) := mul_le_mul_of_nonneg_right hg1 (by linarith)
    rw [hlgc]
    linarith
  have hE : ∀ s ∈ T.filter (fun s => IsV X p s),
      askP X a b p j s + Mn X a b p j s - lgc ≤ gam p * al L a s := by
    intro s hs
    have h1 := ask_add_Mn X P hW hp j (hTT s (Finset.mem_filter.1 hs).1)
    unfold al
    rw [mul_sub]
    linarith
  have hO : ∀ s ∈ T.filter (fun s => ¬ IsV X p s), askP X a b p j s - lgc ≤ gam p * al L a s -
      ∑' e : ℕ, (if Odd e then min (al L a s / (p : ℝ) ^ e) (capU X b p j s e) else 0) := by
    intro s hs
    exact odd_top X P hW hp hj (hTT s (Finset.mem_filter.1 hs).1)
  have sE := Finset.sum_le_sum hE
  have sO := Finset.sum_le_sum hO
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at sE sO
  have a1 := Finset.sum_filter_add_sum_filter_not T (fun s => IsV X p s) (fun s => askP X a b p j s)
  have a2 := Finset.sum_filter_add_sum_filter_not T (fun s => IsV X p s) (fun s => gam p * al L a s)
  have a4 := Finset.sum_filter_add_sum_filter_not T (fun s => IsV X p s) (fun _ => lgc)
  have a5 : ∑ _s ∈ T, lgc = (T.card : ℝ) * lgc := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
  linarith

theorem partner_of_central {p : ℕ} (hc : IsResidueClassZero D p) (s : HH D) (e : ℕ) : partner D p s e = (false, s + e • hP D p) := by
  unfold partner
  rw [decide_eq_false (fun h => not_singular_of_central hc h.1)]

open Classical in
theorem sum_topsOn_V (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0)
    (F : HH D → ℝ) : ∑ s ∈ (topsOn X p t0).filter (fun s => IsV X p s), F s =
      ∑ i ∈ (topsPos D p t0).filter (fun i => IsTypeV i), F (phi D p t0 i) := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_topsOn X hc h0]
  apply Finset.sum_congr rfl
  intro i _
  exact if_congr (isV_phi X hc h0 i) rfl rfl

open Classical in
theorem sum_topsOn_nV (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0)
    (F : HH D → ℝ) : ∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), F s =
      ∑ i ∈ (topsPos D p t0).filter (fun i => ¬ IsTypeV i), F (phi D p t0 i) := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_topsOn X hc h0]
  apply Finset.sum_congr rfl
  intro i _
  exact if_congr (not_congr (isV_phi X hc h0 i)) rfl rfl

open Classical in

theorem kinkHH (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime)
    (hc : IsResidueClassZero D p) (h1 : Even (addOrderOf (hP D p))) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) {j : ℕ}
    (hj : j ∈ SizeData₂.lifts D) :
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (fillG X b j (false, s) - (b s : ℝ))) +
      (∑ y ∈ (topsPos D p t0).filter (fun y => ¬ IsTypeV y),
        (if dMinus (topsPos D p t0) y = 0 then 0 else
          min (wPos D p t0 b y : ℝ) ((wPos D p t0 a (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y)) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y))) ≤
    (∑ s ∈ (topsOn X p t0).filter (fun s => IsV X p s), Mn X a b p j s) +
      (Nv X p t0 : ℝ) * (L.sc.b' / L.sc.x + L.etaSz) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨h500, _, hwb, hcG, _⟩ := base P
  have hx := sc_x_pos L.sc
  have hbx : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx.le
  have hη := L.etaSz_pos
  have hk0 := kaJ_nonneg D j hj
  have hmemT : ∀ y ∈ topsPos D p t0, phi D p t0 y ∈ D.host.TT := fun y hy => (Finset.mem_filter.1 hy).2
  rw [sum_topsOn_nV X hc h0, sum_topsOn_V X hc h0, ← Finset.sum_add_distrib]
  have hk := kink h1 (topsPos D p t0) (p : ℝ) hp2 (fun i => (a (phi D p t0 i) : ℝ))
    (fun i => fill X b j (false, phi D p t0 i))
    (fun x hx => by have := (a_bounds P hW (hmemT x hx)).1; linarith)
    (fun x => by have := fill_ge_one X P hW j (false, phi D p t0 x); linarith)
  have hR : ∑ x ∈ (topsPos D p t0).filter (fun x => IsTypeV x), ∑' e : ℕ, (if Odd e then
      min ((a (phi D p t0 x) : ℝ) / (p : ℝ) ^ e) (fill X b j (false, phi D p t0 (posAdd x e))) else 0) =
      ∑ i ∈ (topsPos D p t0).filter (fun i => IsTypeV i), Mn X a b p j (phi D p t0 i) := by
    apply Finset.sum_congr rfl
    intro x _
    unfold Mn
    apply tsum_congr
    intro e
    rw [partner_of_central hc, phi_posAdd]
  rw [hR] at hk
  have hterm : ∀ y ∈ (topsPos D p t0).filter (fun y => ¬ IsTypeV y),
      (fillG X b j (false, phi D p t0 y) - (b (phi D p t0 y) : ℝ)) +
        (if dMinus (topsPos D p t0) y = 0 then 0 else
          min (wPos D p t0 b y : ℝ) ((wPos D p t0 a (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y)) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y)) ≤
      (if dMinus (topsPos D p t0) y = 0 then 0 else
          min (fill X b j (false, phi D p t0 y))
            ((a (phi D p t0 (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y))) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y)) + (L.sc.b' / L.sc.x + L.etaSz) := by
    intro y hy
    have hyT := hmemT y (Finset.mem_filter.1 hy).1
    have hf : fill X b j (false, phi D p t0 y) = (b (phi D p t0 y) : ℝ) + X.off j (false, phi D p t0 y) := by
      unfold fill
      rw [if_pos ⟨rfl, hyT⟩]
    obtain ⟨o1, o2⟩ := X.off_top j (false, phi D p t0 y) ⟨rfl, hyT⟩
    unfold fillG
    rw [hf]
    split_ifs with hd
    · linarith
    · have hm : min (wPos D p t0 b y : ℝ)
          ((wPos D p t0 a (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y)) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y) ≤
          min ((b (phi D p t0 y) : ℝ) + X.off j (false, phi D p t0 y))
            ((a (phi D p t0 (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y))) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y) := by
        apply min_le_min
        · show (b (phi D p t0 y) : ℝ) ≤ _
          linarith
        · exact le_rfl
      linarith
  have hs := Finset.sum_le_sum hterm
  have hcard : (((topsPos D p t0).filter (fun y => ¬ IsTypeV y)).card : ℝ) ≤ (Nv X p t0 : ℝ) := by
    rw [Nv_eq_card X hc h0]
    exact_mod_cast Finset.card_filter_le _ _
  have hmul := mul_le_mul_of_nonneg_right hcard (by linarith : 0 ≤ L.sc.b' / L.sc.x + L.etaSz)
  refine le_trans hs ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

structure NumStar (D : D7) (L : SizeData₂ D) (K : Consts) (C31 C bo : ℝ) : Prop where

  hL2 : L2 D L.sc < goodU L.sc.delta1

  h3G : ((3 * Gp L.sc : ℕ) : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4)
  hlx : 1 ≤ Real.log L.sc.x

  hGu : C31 * Real.log L.sc.x / L.sc.delta1 * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) ≤ L.sc.b'

  hc0 : c0num L ≤ 3 * L.sc.b'

  hkQ : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → (D.R.k : ℝ) * Qp L.sc p ≤ L.sc.b'

  hDII : ∀ p : ℕ, p.Prime →
    K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a ≤ L.sc.b'
  hC3 : 3 ≤ C

  hCt : K.tII * (rG L.sc : ℝ) ≤ C
  hCD : 2 * (3 : ℝ) + 4 * K.tII + 160 * C31 + 7 ≤ C
  hCP : K.Pr1 * C31 ≤ C

  hN1 : K.kappaThresholdOne * (N1 L.sc : ℝ) ≤ C * Real.log L.sc.x

  hbo : ∀ p : ℕ, p.Prime → L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ∀ n' : ℕ, n' ≤ D.R.n →
    K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * (L.etaSz + cG L + Nm D) +
      K.kappaThresholdTwo * (Qp L.sc p * c6f K L p n' +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) +
      2 * (C31 * Real.log L.sc.x / L.sc.delta1) * cG L +
      40 * C31 * Real.log L.sc.x * (K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) + 3 ≤ bo

theorem orbit_facts (X : Inst D L) {K : Consts} {C31 C bo : ℝ} (A1 : adm1 D L X C31) (hC31 : 0 < C31)
    (Nn : NumStar D L K C31 C bo) {p : ℕ} (hcand : Cand D L K p) {t0 : HH D} (ht0 : t0 ∈ goodReps X p) :
    (1 : ℝ) ≤ (Nv X p t0 : ℝ) ∧
    (addOrderOf (hP D p) : ℝ) * L.sc.delta1 ≤ (Nv X p t0 : ℝ) * (C31 * Real.log L.sc.x) ∧
    (addOrderOf (hP D p) : ℝ) ≤ (Nv X p t0 : ℝ) * (C31 * Real.log L.sc.x / L.sc.delta1) := by
  classical
  obtain ⟨hp, hX, hc, hord, _⟩ := hcand
  have h3 : 3 * Gp L.sc ≤ addOrderOf (hP D p) := by exact_mod_cast le_trans Nn.h3G hord
  obtain ⟨hr, hg⟩ := Finset.mem_filter.1 ht0
  have h := (A1 p hp hc hord Nn.hL2 h3 t0 hr hg).1.1
  have hpos : 0 < C31 * Real.log L.sc.x := mul_pos hC31 (by have := Nn.hlx; linarith)
  have hδ := sc_delta1_pos L.sc
  rw [div_le_iff₀ hpos] at h
  have hn1 : (1 : ℝ) ≤ (addOrderOf (hP D p) : ℝ) := by exact_mod_cast addOrderOf_pos (hP D p)
  have hN0 : 0 < (Nv X p t0 : ℝ) := by
    by_contra hcon
    have h0 : (Nv X p t0 : ℝ) ≤ 0 := not_lt.1 hcon
    have h1 : (Nv X p t0 : ℝ) * (C31 * Real.log L.sc.x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hpos.le
    have h2 : 0 < (addOrderOf (hP D p) : ℝ) * L.sc.delta1 := mul_pos (by linarith) hδ
    linarith
  refine ⟨?_, h, ?_⟩
  · have : 0 < Nv X p t0 := by exact_mod_cast hN0
    exact_mod_cast this
  · rw [← mul_div_assoc, le_div_iff₀ hδ]
    exact h

theorem caseD_arith (N n nd r lx b' G u c c0 kQ S1 Dw C31 Pr2 tc C : ℝ)
    (hN : 1 ≤ N) (hn0 : 0 ≤ n) (_hnd0 : 0 ≤ nd) (hr : 1 ≤ r) (hlx : 1 ≤ lx) (hb : 1 ≤ b') (hnG : n ≤ N * G)
    (hnd : nd ≤ N * (C31 * lx)) (hGu : G * u ≤ b') (hc0' : 0 ≤ c) (hcu : c ≤ u) (hc03 : c0 ≤ 3 * b')
    (hc00 : 0 ≤ c0) (hkQ : kQ ≤ b') (hS1 : 0 ≤ S1) (hDw0 : 0 ≤ Dw) (hDw : Dw ≤ b') (hPr2 : 0 ≤ Pr2)
    (htc : 0 ≤ tc) (hC31 : 0 ≤ C31) (hC1 : tc * r ≤ C) (hC2 : 2 * Pr2 + 4 * tc + 160 * C31 + 7 ≤ C) :
    Pr2 * r * (N * b' + n * u) + (tc * r * N * (S1 + c0 + kQ) + 2 * r * n * c + 1) +
      (40 * nd * Dw + 2 * r * n * c + r * (40 * nd) * c0 + 1) + 1 ≤ N * (C * r * b' * lx + C * lx * S1) := by
  have hu0 : 0 ≤ u := le_trans hc0' hcu
  have hN0 : 0 ≤ N := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hb0 : 0 ≤ b' := by linarith
  have hlx0 : 0 ≤ lx := by linarith
  have hC0 : 0 ≤ C := by linarith
  have t1 : n * u ≤ N * b' := by
    calc n * u ≤ N * G * u := mul_le_mul_of_nonneg_right hnG hu0
      _ = N * (G * u) := by ring
      _ ≤ N * b' := mul_le_mul_of_nonneg_left hGu hN0
  have t2 : n * c ≤ N * b' := le_trans (mul_le_mul_of_nonneg_left hcu hn0) t1
  have hZ : 1 ≤ N * b' := by nlinarith
  have hZ0 : 0 ≤ N * b' := by linarith
  have hCl0 : 0 ≤ C31 * lx := mul_nonneg hC31 hlx0
  have t3 : nd * Dw ≤ C31 * (N * b' * lx) := by
    calc nd * Dw ≤ N * (C31 * lx) * Dw := mul_le_mul_of_nonneg_right hnd hDw0
      _ ≤ N * (C31 * lx) * b' := mul_le_mul_of_nonneg_left hDw (mul_nonneg hN0 hCl0)
      _ = C31 * (N * b' * lx) := by ring
  have t4 : nd * c0 ≤ 3 * (C31 * (N * b' * lx)) := by
    calc nd * c0 ≤ N * (C31 * lx) * c0 := mul_le_mul_of_nonneg_right hnd hc00
      _ ≤ N * (C31 * lx) * (3 * b') := mul_le_mul_of_nonneg_left hc03 (mul_nonneg hN0 hCl0)
      _ = 3 * (C31 * (N * b' * lx)) := by ring
  have y0 : N * b' ≤ N * b' * r := le_mul_of_one_le_right hZ0 hr
  have y1 : N * b' * r ≤ N * b' * r * lx := le_mul_of_one_le_right (by linarith) hlx
  have y2 : N * b' * lx ≤ N * b' * r * lx := by
    have := mul_le_mul_of_nonneg_right y0 hlx0
    linarith
  have B1 : Pr2 * r * (n * u) ≤ Pr2 * r * (N * b') := mul_le_mul_of_nonneg_left t1 (mul_nonneg hPr2 hr0)
  have B2 : Pr2 * (N * b' * r) ≤ Pr2 * (N * b' * r * lx) := mul_le_mul_of_nonneg_left y1 hPr2
  have B3 : tc * r * N * (c0 + kQ) ≤ tc * r * N * (4 * b') :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg htc hr0) hN0)
  have B4 : tc * (N * b' * r) ≤ tc * (N * b' * r * lx) := mul_le_mul_of_nonneg_left y1 htc
  have B5 : tc * r * (N * S1) ≤ C * (N * S1) := mul_le_mul_of_nonneg_right hC1 (mul_nonneg hN0 hS1)
  have B6 : C * (N * S1) ≤ C * (N * S1) * lx := le_mul_of_one_le_right (mul_nonneg hC0 (mul_nonneg hN0 hS1)) hlx
  have B7 : r * (n * c) ≤ r * (N * b') := mul_le_mul_of_nonneg_left t2 hr0
  have BetaSesquilinearity : C31 * (N * b' * lx) ≤ C31 * (N * b' * r * lx) := mul_le_mul_of_nonneg_left y2 hC31
  have B9 : r * (nd * c0) ≤ r * (3 * (C31 * (N * b' * lx))) := mul_le_mul_of_nonneg_left t4 hr0
  have lowerOffDiagonalCoeff : (2 * Pr2 + 4 * tc + 160 * C31 + 7) * (N * b' * r * lx) ≤ C * (N * b' * r * lx) :=
    mul_le_mul_of_nonneg_right hC2 (by linarith)
  nlinarith [B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, B9, lowerOffDiagonalCoeff, t3, y0, y1, y2, hZ]

theorem caseE_arith (N n nd lx G w η c Nm S2 B1 E tN1 Pr1 kappaThresholdTwo C31 C bo Cw : ℝ)
    (hN : 1 ≤ N) (hnG : n ≤ N * G) (hnd : nd ≤ N * (C31 * lx)) (hw : 0 ≤ w) (hη : 0 ≤ η) (hc : 0 ≤ c)
    (hNm : 0 ≤ Nm) (hS2 : 0 ≤ S2) (hE : 0 ≤ E) (hPr1 : 0 ≤ Pr1) (hGw : Pr1 * G * w ≤ Cw)
    (htN1 : tN1 ≤ C * lx)
    (hbo : Pr1 * G * (η + c + Nm) + kappaThresholdTwo * B1 + 2 * G * c + 40 * C31 * lx * E + 3 ≤ bo) :
    Pr1 * n * (w + η + c + Nm) + (tN1 * N * S2 + kappaThresholdTwo * N * B1 + 2 * n * c + 1) + (40 * nd * E + 1) + 1 ≤
      N * (Cw + bo + C * lx * S2) := by
  have hN0 : 0 ≤ N := by linarith
  have A1 : Pr1 * n * (w + η + c + Nm) ≤ Pr1 * (N * G) * (w + η + c + Nm) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnG hPr1) (by linarith)
  have A2 : n * c ≤ N * G * c := mul_le_mul_of_nonneg_right hnG hc
  have A3 : nd * E ≤ N * (C31 * lx) * E := mul_le_mul_of_nonneg_right hnd hE
  have A4 := mul_le_mul_of_nonneg_left hbo hN0
  have A5 := mul_le_mul_of_nonneg_left hGw hN0
  have A6 : tN1 * (N * S2) ≤ C * lx * (N * S2) := mul_le_mul_of_nonneg_right htN1 (mul_nonneg hN0 hS2)
  nlinarith [A1, A2, A3, A4, A5, A6]

theorem lg_ge_one (P : ParameterChoice' D L) {p : ℕ} (hp : p.Prime) (hX : (p : ℝ) < L.sc.X') :
    1 ≤ Real.logb p (2 * L.sc.a) := by
  obtain ⟨h500, _, hwb, _, _⟩ := base P
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hXpos : 0 < L.sc.X' := by unfold Scale.X'; exact Real.exp_pos _
  have ha := sc_one_lt_a L.sc
  have hb : 1 ≤ L.sc.a / L.sc.X' := by
    have : L.sc.b' = L.sc.a / L.sc.X' := rfl
    linarith
  rw [one_le_div hXpos] at hb
  rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]
  linarith

theorem lo_D (K : Consts) (L : SizeData₂ D) (C bo : ℝ) {p : ℕ} (hc : IsResidueClassZero D p) (h0 : (p : ℝ) < L.sc.p0 D.R.k)
    (hX : (p : ℝ) < L.sc.X') : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
      C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x +
      C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) := by
  simp only [lo, if_pos hc, if_pos h0, if_pos (And.intro hc hX)]

theorem lo_E (K : Consts) (L : SizeData₂ D) (C bo : ℝ) {p : ℕ} (hc : IsResidueClassZero D p) (h0 : L.sc.p0 D.R.k ≤ (p : ℝ))
    (hX : (p : ℝ) < L.sc.X') : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
      (L.sc.b' / L.sc.x + L.etaSz + C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 + bo) +
      C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2) := by
  simp only [lo, if_pos hc, if_neg (not_lt.2 h0), if_pos hX, if_pos (And.intro hc hX)]

theorem La_nonneg (K : Consts) (hLa : 0 ≤ K.La) (s : Scale) : 0 ≤ La K s := by
  unfold La
  exact mul_nonneg (mul_nonneg hLa (by positivity)) (Real.log_nonneg (sc_one_lt_a s).le)

theorem rG_ge_one (s : Scale) : (1 : ℝ) ≤ (rG s : ℝ) := by
  unfold rG
  push_cast
  have : (0 : ℝ) ≤ (KG s : ℝ) := Nat.cast_nonneg _
  linarith

theorem starAt_D (X : Inst D L) {K : Consts} (hK : K.Nonneg) (P : ParameterChoice' D L) {C31 C bo : ℝ}
    (A1 : adm1 D L X C31) (hC31 : 0 < C31) (Nn : NumStar D L K C31 C bo) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hcand : Cand D L K p) (h0 : (p : ℝ) < L.sc.p0 D.R.k) {t0 : HH D} (ht0 : t0 ∈ goodReps X p) {j : ℕ}
    (hj : j ∈ SizeData₂.lifts D) : StarAt X K C bo a b p j t0 := by
  classical
  obtain ⟨hN1, hnd, hnG⟩ := orbit_facts X A1 hC31 Nn hcand ht0
  obtain ⟨hp, hX, hc, hord, _⟩ := hcand
  obtain ⟨hLa, _, _, htII, hDII, _, _, _, _, _, _, _, _, _, _⟩ := hK
  obtain ⟨h500, hcw, hwb, hc0, _⟩ := base P
  have hlg := lg_ge_one P hp hX
  have hgl := gU_lower X K P hW hp hlg hj t0
  have hMn : 0 ≤ ∑ s ∈ (topsOn X p t0).filter (fun s => IsV X p s), Mn X a b p j s :=
    Finset.sum_nonneg (fun s hs => Mn_nonneg X P hW j (Finset.mem_filter.1 (Finset.mem_filter.1 hs).1).1)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have ha := sc_one_lt_a L.sc
  have hη := L.etaSz_pos
  have hδ := sc_delta1_pos L.sc
  have hr := rG_ge_one L.sc
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (addOrderOf (hP D p) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hlp : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 ha.le
  have hQ0 : 0 ≤ Qp L.sc p := by unfold Qp; positivity
  have hc00 : 0 ≤ c0num L := by unfold c0num; linarith
  have hS1 : 0 ≤ La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) :=
    add_nonneg (div_nonneg (mul_nonneg (La_nonneg K hLa _) (by linarith)) (mul_nonneg hp0.le hk0))
      (mul_nonneg (by linarith) (Real.rpow_nonneg hp0.le _))
  have hDw0 : 0 ≤ K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a :=
    mul_nonneg (mul_nonneg hDII (by positivity)) hlp
  have har := caseD_arith (Nv X p t0 : ℝ) (addOrderOf (hP D p) : ℝ) ((addOrderOf (hP D p) : ℝ) * L.sc.delta1)
    (rG L.sc : ℝ) (Real.log L.sc.x) L.sc.b' (C31 * Real.log L.sc.x / L.sc.delta1)
    (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) (cG L) (c0num L) ((D.R.k : ℝ) * Qp L.sc p)
    (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)))
    (K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a) C31 3 K.tII C
    hN1 hn0 (mul_nonneg hn0 hδ.le) hr Nn.hlx (by linarith) hnG hnd Nn.hGu hc0 (by linarith) Nn.hc0 hc00
    (Nn.hkQ p hp h0) hS1 hDw0 (Nn.hDII p hp) (by norm_num) htII hC31.le Nn.hCt Nn.hCD
  have hPr : Pr X K b p j t0 ≤ 3 * (rG L.sc : ℝ) * ((Nv X p t0 : ℝ) * L.sc.b' +
      (addOrderOf (hP D p) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)) := by
    unfold Pr
    rw [if_neg (not_le.2 h0), partner_count_of_central hc]
    have e1 : (Nv X p t0 : ℝ) * (2 * L.sc.b' + cG L) ≤ (Nv X p t0 : ℝ) * (3 * L.sc.b') :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : 0 ≤ (addOrderOf (hP D p) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) :=
      mul_nonneg hn0 (by linarith)
    have e3 : (Nv X p t0 : ℝ) * (2 * L.sc.b' + cG L) +
        (addOrderOf (hP D p) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) ≤
        3 * ((Nv X p t0 : ℝ) * L.sc.b' +
          (addOrderOf (hP D p) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)) := by linarith
    have e4 := mul_le_mul_of_nonneg_left e3 (by linarith : (0 : ℝ) ≤ (rG L.sc : ℝ))
    linarith
  have htv : tv X K a b p t0 = tIIf K L p (addOrderOf (hP D p)) (Nv X p t0) := by
    unfold tv
    rw [if_pos h0, partner_count_of_central hc]
  have hDp : Dp K L p = DIIf K L p (addOrderOf (hP D p)) := by
    unfold Dp
    rw [if_pos h0, partner_count_of_central hc]
  have hN0 : (0 : ℝ) ≤ (Nv X p t0 : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ (rG L.sc : ℝ) := by linarith
  have ht0' : 0 ≤ tIIf K L p (addOrderOf (hP D p)) (Nv X p t0) := by
    unfold tIIf
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg htII hr0) hN0)
      (by have := mul_nonneg hk0 hQ0; linarith)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) hn0) hc0)
  have hceil := (Nat.ceil_lt_add_one ht0').le
  have hNp0 : 0 ≤ NplusF L.sc (addOrderOf (hP D p)) := by
    unfold NplusF
    exact mul_nonneg (mul_nonneg (by norm_num) hn0) hδ.le
  have hD := (Nat.ceil_lt_add_one (a := K.DII * NplusF L.sc (addOrderOf (hP D p)) *
      ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
      Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (addOrderOf (hP D p) : ℝ) * cG L +
      (rG L.sc : ℝ) * NplusF L.sc (addOrderOf (hP D p)) * c0num L)
    (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hDII hNp0) (by positivity)) hlp)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) hn0) hc0)) (mul_nonneg (mul_nonneg hr0 hNp0) hc00))).le
  have hs : (Nv X p t0 : ℝ) * (3 * cG L * Real.logb p (2 * L.sc.a)) ≤
      (Nv X p t0 : ℝ) * (C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)) := by
    apply mul_le_mul_of_nonneg_left _ hN0
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have h1 := mul_le_mul_of_nonneg_right Nn.hC3 hc0
    have h2 : 0 ≤ C * L.etaSz := mul_nonneg (by linarith [Nn.hC3]) hη.le
    linarith
  unfold StarAt
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, lo_D K L C bo hc h0 hX, htv, hDp]
  have hcard : ((topsOn X p t0).card : ℝ) = (Nv X p t0 : ℝ) := rfl
  rw [hcard]
  unfold tIIf at hceil
  unfold NplusF at hD
  have hDD : (DIIf K L p (addOrderOf (hP D p)) : ℝ) ≤ K.DII * (40 * (addOrderOf (hP D p) : ℝ) * L.sc.delta1) *
      ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
      Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (addOrderOf (hP D p) : ℝ) * cG L +
      (rG L.sc : ℝ) * (40 * (addOrderOf (hP D p) : ℝ) * L.sc.delta1) * c0num L + 1 := hD
  unfold tIIf
  linarith [hgl, hMn, har, hceil, hDD, hs, hPr]

theorem order_le_n (D : D7) (h : HH D) : addOrderOf h ≤ D.R.n := by
  have hd : addOrderOf h ∣ D.R.ord := by
    have := addOrderOf_dvd_card (x := h)
    rwa [D.R.card_A] at this
  exact Nat.le_of_dvd D.R.ord_pos hd

theorem starAt_E (X : Inst D L) {K : Consts} (hK : K.Nonneg) (P : ParameterChoice' D L) {C31 C bo : ℝ}
    (A1 : adm1 D L X C31) (hC31 : 0 < C31) (Nn : NumStar D L K C31 C bo) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hcand : Cand D L K p) (h0 : L.sc.p0 D.R.k ≤ (p : ℝ)) {t0 : HH D} (ht0 : t0 ∈ goodReps X p) {j : ℕ}
    (hj : j ∈ SizeData₂.lifts D) : StarAt X K C bo a b p j t0 := by
  classical
  obtain ⟨hN1, hnd, hnG⟩ := orbit_facts X A1 hC31 Nn hcand ht0
  obtain ⟨hp, hX, hc, hord, _⟩ := hcand
  obtain ⟨hLa, _, _, _, _, _, _, hDI, htI1, htI2, _, _, _, hPr1, _⟩ := hK
  obtain ⟨h500, hcw, hwb, hc0, _⟩ := base P
  have hfix : X.bs (stepP D p) t0 = t0 := reps_fix X (Finset.mem_filter.1 ht0).1
  have hord1 : 1 < addOrderOf (hP D p) := by
    have h1 : (1 : ℝ) < L.sc.x ^ (L.sc.eps / 4) :=
      Real.one_lt_rpow L.sc.one_lt_alt (by have := L.sc.eps_pos; positivity)
    exact_mod_cast lt_of_lt_of_le h1 hord
  have hlg := lg_ge_one P hp hX
  have hgl := gU_lower X K P hW hp hlg hj t0
  have hkk := kinkHH X P hW hp hc (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hord) hfix hj
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have ha := sc_one_lt_a L.sc
  have hη := L.etaSz_pos
  have hδ := sc_delta1_pos L.sc
  have hlx := Nn.hlx
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (addOrderOf (hP D p) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hlp : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 ha.le
  have hQ0 : 0 ≤ Qp L.sc p := by unfold Qp; positivity
  have hN0 : (0 : ℝ) ≤ (Nv X p t0 : ℝ) := by linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by linarith
  have hS2 : 0 ≤ L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) :=
    add_nonneg (div_nonneg (by linarith) (by positivity))
      (div_nonneg (mul_nonneg (La_nonneg K hLa _) (by linarith)) (mul_nonneg hp0.le hk0))
  have hE0 : 0 ≤ K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a :=
    mul_nonneg (mul_nonneg (mul_nonneg hDI (by positivity)) (by positivity)) hlp
  have hnle : addOrderOf (hP D p) ≤ D.R.n := order_le_n D _
  have hNle : Nv X p t0 ≤ D.R.n := by
    rw [Nv_eq_card X hc hfix]
    refine le_trans (Finset.card_le_univ _) ?_
    rw [Fintype.card_fin]
    exact hnle
  have hGw : K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * L.sc.w'' D.R.n ≤
      C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 := by
    have h1 : 0 ≤ L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
      div_nonneg (mul_nonneg hw0 (by linarith)) hδ.le
    have h2 := mul_le_mul_of_nonneg_right Nn.hCP h1
    calc K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * L.sc.w'' D.R.n
        = K.Pr1 * C31 * (L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1) := by ring
      _ ≤ C * (L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1) := h2
      _ = C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 := by ring
  have hNp0 : 0 ≤ NplusF L.sc (addOrderOf (hP D p)) := by
    unfold NplusF
    exact mul_nonneg (mul_nonneg (by norm_num) hn0) hδ.le
  have hB0 : 0 ≤ Qp L.sc p * c6f K L p (addOrderOf (hP D p)) +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L := by
    have e1 : (0 : ℝ) ≤ (DIf K L p (addOrderOf (hP D p)) : ℝ) := Nat.cast_nonneg _
    have e2 : 0 ≤ K.kappaThresholdTwo * NplusF L.sc (addOrderOf (hP D p)) * (D.R.k : ℝ) * Real.logb p L.sc.a :=
      mul_nonneg (mul_nonneg (mul_nonneg htI2 hNp0) hk0) hlp
    have e3 : 0 ≤ 4 * NplusF L.sc (addOrderOf (hP D p)) * cG L := mul_nonneg (mul_nonneg (by norm_num) hNp0) hc0
    have e4 : 0 ≤ 2 * (addOrderOf (hP D p) : ℝ) * cG L := mul_nonneg (mul_nonneg (by norm_num) hn0) hc0
    have e5 := mul_nonneg hk0 hQ0
    have e6 := mul_nonneg hk0 hlp
    have e7 : 0 ≤ Qp L.sc p * c6f K L p (addOrderOf (hP D p)) := mul_nonneg hQ0 (by unfold c6f; linarith)
    linarith
  have har := caseE_arith (Nv X p t0 : ℝ) (addOrderOf (hP D p) : ℝ) ((addOrderOf (hP D p) : ℝ) * L.sc.delta1)
    (Real.log L.sc.x) (C31 * Real.log L.sc.x / L.sc.delta1) (L.sc.w'' D.R.n) L.etaSz (cG L) (Nm D)
    (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))
    (Qp L.sc p * c6f K L p (addOrderOf (hP D p)) +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L)
    (K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a)
    (K.kappaThresholdOne * (N1 L.sc : ℝ)) K.Pr1 K.kappaThresholdTwo C31 C bo (C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1)
    hN1 hnG hnd hw0 hη.le hc0 hNm0 hS2 hE0 hPr1 hGw Nn.hN1
    (Nn.hbo p hp h0 hX (addOrderOf (hP D p)) hnle)
  have hPr : Pr X K b p j t0 =
      (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (fillG X b j (false, s) - (b s : ℝ))) +
      K.Pr1 * (addOrderOf (hP D p) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) := by
    unfold Pr
    rw [if_pos h0, partner_count_of_central hc]
  have htv : tv X K a b p t0 =
      tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b) := by
    unfold tv
    rw [if_neg (not_lt.2 h0)]
  have hDp : Dp K L p = DIf K L p (addOrderOf (hP D p)) := by
    unfold Dp
    rw [if_neg (not_lt.2 h0), partner_count_of_central hc]

  have hKk : 0 ≤ ∑ y ∈ (topsPos D p t0).filter (fun y => ¬ IsTypeV y),
        (if dMinus (topsPos D p t0) y = 0 then 0 else
          min (wPos D p t0 b y : ℝ) ((wPos D p t0 a (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y)) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y)) := by
    apply Finset.sum_nonneg
    intro y hy
    split_ifs with hd
    · exact le_rfl
    · have hyT : phi D p t0 y ∈ D.host.TT := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
      have hxT : phi D p t0 (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y)) ∈ D.host.TT :=
        (Finset.mem_filter.1 (dMinus_spec _ y hd).2.2.1).2
      apply le_min
      · have := (hW _ hyT).2.2
        show (0 : ℝ) ≤ (b (phi D p t0 y) : ℝ)
        linarith
      · apply div_nonneg _ (by positivity)
        have := (a_bounds P hW hxT).1
        show (0 : ℝ) ≤ (a (phi D p t0 (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y))) : ℝ)
        linarith
  have hcardN : ((topsPos D p t0).card : ℝ) = (Nv X p t0 : ℝ) := by rw [Nv_eq_card X hc hfix]
  have htIf : tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b) =
      (∑ y ∈ (topsPos D p t0).filter (fun y => ¬ IsTypeV y),
        (if dMinus (topsPos D p t0) y = 0 then 0 else
          min (wPos D p t0 b y : ℝ) ((wPos D p t0 a (posAdd y (addOrderOf (hP D p) - dMinus (topsPos D p t0) y)) : ℝ) /
            (p : ℝ) ^ dMinus (topsPos D p t0) y))) +
      K.kappaThresholdOne * (Nv X p t0 : ℝ) * (N1 L.sc : ℝ) *
        (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
      K.kappaThresholdTwo * (Nv X p t0 : ℝ) * (Qp L.sc p * c6f K L p (addOrderOf (hP D p)) +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) +
      2 * (addOrderOf (hP D p) : ℝ) * cG L := by
    unfold tIf
    rw [hcardN]
  have ht0' : 0 ≤ tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b) := by
    rw [htIf]
    have e1 : 0 ≤ K.kappaThresholdOne * (Nv X p t0 : ℝ) * (N1 L.sc : ℝ) *
        (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) :=
      mul_nonneg (mul_nonneg (mul_nonneg htI1 hN0) (Nat.cast_nonneg _)) hS2
    have e2 := mul_nonneg (mul_nonneg htI2 hN0) hB0
    have e3 : 0 ≤ 2 * (addOrderOf (hP D p) : ℝ) * cG L := mul_nonneg (mul_nonneg (by norm_num) hn0) hc0
    linarith
  have hceil := (Nat.ceil_lt_add_one ht0').le
  have hD := (Nat.ceil_lt_add_one (a := K.DI * NplusF L.sc (addOrderOf (hP D p)) * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
      ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hDI hNp0) (by positivity)) (by positivity)) hlp)).le
  unfold NplusF at hD
  have hDD : (DIf K L p (addOrderOf (hP D p)) : ℝ) ≤ K.DI * (40 * (addOrderOf (hP D p) : ℝ) * L.sc.delta1) *
      (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a + 1 := hD
  have hs : (Nv X p t0 : ℝ) * (3 * cG L * Real.logb p (2 * L.sc.a)) ≤
      (Nv X p t0 : ℝ) * (C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)) := by
    apply mul_le_mul_of_nonneg_left _ hN0
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have h1 := mul_le_mul_of_nonneg_right Nn.hC3 hc0
    have h2 : 0 ≤ C * L.etaSz := mul_nonneg (by linarith [Nn.hC3]) hη.le
    linarith
  unfold StarAt
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, lo_E K L C bo hc h0 hX, hPr, htv, hDp]
  have hcard : ((topsOn X p t0).card : ℝ) = (Nv X p t0 : ℝ) := rfl
  rw [hcard]
  linarith [hgl, hkk, har, hceil, hDD, hs, htIf]

theorem starAll_of (X : Inst D L) {K : Consts} (hK : K.Nonneg) (P : ParameterChoice' D L) {C31 C bo : ℝ}
    (A1 : adm1 D L X C31) (hC31 : 0 < C31) (Nn : NumStar D L K C31 C bo) : StarAll X K C bo := by
  intro a b hW p hcand t0 ht0 j hj
  rcases lt_or_ge (p : ℝ) (L.sc.p0 D.R.k) with h0 | h0
  · exact starAt_D X hK P A1 hC31 Nn hW hcand h0 ht0 hj
  · exact starAt_E X hK P A1 hC31 Nn hW hcand h0 ht0 hj

end Formalism.MainNotions.AuxBlock8.Pf.St

end
