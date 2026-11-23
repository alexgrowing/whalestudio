import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleM

noncomputable section

namespace PI.WGL.LTB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem initMinor_perm {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (σ : Equiv.Perm (Fin s)) :
    initMinor R (n := m) (I ∘ σ) hs = (Equiv.Perm.sign σ : ℤ) • initMinor R (n := m) I hs := by
  unfold initMinor
  first
  | (rw [zsmul_eq_mul, ← Matrix.det_permute]; rfl)
  | (rw [← Units.smul_def, ← Matrix.det_permute]; rfl)

theorem initMinor_not_inj {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (hI : ¬ Function.Injective I) : initMinor R (n := m) I hs = 0 := by
  unfold initMinor
  unfold Function.Injective at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq hne (by ext q; simp [hij])

theorem initMinor_std {R : Type*} [CommRing R] {r m s : ℕ} (hr : s ≤ r) (hs : s ≤ m) :
    initMinor R (n := m) (fun p : Fin s => (⟨p.1, lt_of_lt_of_le p.2 hr⟩ : Fin r)) hs = lpMinor R s hr hs := by
  rfl

theorem unl_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) (σ : Equiv.Perm (Fin m)) :
    unl h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • unl h ρ hm := by
  unfold unl
  exact initMinor_perm (eRow h ∘ ρ) hm σ

theorem liftRows_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (σ : Equiv.Perm (Fin m)) :
    liftRows h (ρ ∘ σ) = liftRows h ρ ∘ (σ.viaFintypeEmbedding Fin.castSuccEmb) := by
  funext p
  induction p using Fin.lastCases with
  | last =>
    have hnot : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
      rintro ⟨y, hy⟩
      have h1 : y.val = m := by
        have := congrArg Fin.val hy
        exact this
      have h2 := y.2
      omega
    rw [Function.comp_apply]
    first
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range hnot]
    simp [liftRows]
  | cast i =>
    rw [Function.comp_apply]
    have e := Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i
    rw [show Fin.castSucc i = (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i from rfl, e]
    simp [liftRows]

theorem lif_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (σ : Equiv.Perm (Fin m)) :
    lif h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • lif h ρ hm := by
  unfold lif
  rw [liftRows_perm, initMinor_perm]
  rw [show Equiv.Perm.sign (σ.viaFintypeEmbedding Fin.castSuccEmb) = Equiv.Perm.sign σ from
    Equiv.Perm.sign_extendDomain σ _]

theorem unl_not_inj {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N)
    (hρ : ¬ Function.Injective ρ) : unl h ρ hm = 0 := by
  unfold unl
  exact initMinor_not_inj _ hm (fun hinj => hρ hinj.of_comp)

theorem lif_not_inj {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (hρ : ¬ Function.Injective ρ) : lif h ρ hm = 0 := by
  unfold lif
  refine initMinor_not_inj _ hm (fun hinj => hρ (fun a b hab => ?_))
  have h2 : liftRows h ρ (Fin.castSucc a) = liftRows h ρ (Fin.castSucc b) := by
    simp [liftRows, hab]
  exact Fin.castSucc_inj.mp (hinj h2)

theorem sum_cnt_lt {n K : ℕ} {sz : Fin K → ℕ} (J : ∀ k, Fin (sz k) → Fin n) (t : ℕ) :
    ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), tupCnt J a := by
  unfold tupCnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := J k) (t := Finset.univ.filter fun a : Fin n => a.1 < t)
    (by intro p hp; simpa using hp)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact ⟨by rw [hp]; exact ha, hp⟩

private theorem card_filter_fin_val_lt' {n c : ℕ} (hc : c ≤ n) :
    (Finset.univ.filter fun a : Fin n => a.1 < c).card = c := by
  have e : (Finset.univ.filter fun a : Fin n => a.1 < c).card = (Finset.range c).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      simpa using ha
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      have hb' : b < c := by simpa using hb
      exact ⟨⟨b, by omega⟩, by simpa using hb', rfl⟩
  rw [e, Finset.card_range]

theorem sum_shape_lt {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (t : ℕ) (ht : t ≤ n) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), shapeDeg sz a = ∑ k, min t (sz k) := by
  unfold shapeDeg
  have e : ∀ k : Fin K, min t (sz k) = (Finset.univ.filter fun a : Fin n => a.1 < t ∧ a.1 < sz k).card := by
    intro k
    rw [← card_filter_fin_val_lt' (n := n) (c := min t (sz k)) (le_trans (min_le_left _ _) ht)]
    apply congrArg Finset.card
    ext a
    simp [lt_min_iff]
  simp only [e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : a.1 < t <;> simp [ha]

theorem top_entries {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hc : tupCnt J = shapeDeg sz) : ∀ k p, (J k p).1 < sz k := by
  intro k p
  have key : ∀ t, t ≤ n → ∀ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = min t (sz k) := by
    intro t ht
    have hle : ∀ k ∈ Finset.univ, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card ≤ min t (sz k) := by
      intro k _
      refine le_min ?_ ?_
      · calc _ ≤ (Finset.univ.filter fun a : Fin n => a.1 < t).card :=
              Finset.card_le_card_of_injOn (J k) (by intro p hp; simpa using hp)
                (by intro a _ b _ hab; exact hinj k hab)
          _ = t := card_filter_fin_val_lt' ht
      · exact (Finset.card_filter_le _ _).trans (by simp)
    have hsum : ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = ∑ k, min t (sz k) := by
      rw [sum_cnt_lt J t, hc, sum_shape_lt sz hsz t ht]
    exact fun k => (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_univ _)
  have h1 := key (sz k) (hsz k) k
  rw [min_self] at h1
  have h2 : (Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h1]
    simp
  have h3 : p ∈ Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k := by
    rw [h2]
    exact Finset.mem_univ _
  simpa using h3

theorem top_perm {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hlt : ∀ k p, (J k p).1 < sz k) :
    ∀ k, ∃ σ : Equiv.Perm (Fin (sz k)), J k = stdT sz hsz k ∘ σ := by
  intro k
  let f : Fin (sz k) → Fin (sz k) := fun p => ⟨(J k p).1, hlt k p⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj k
    exact Fin.ext (by simpa [f] using congrArg Fin.val hab)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  funext p
  exact Fin.ext rfl

theorem card_eq_val {m n : ℕ} (a : Fin n) :
    (Finset.univ.filter fun p : Fin m => p.1 = a.1).card = if a.1 < m then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨⟨a.1, h⟩, ?_⟩
    ext p
    simp [Fin.ext_iff]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    exact h (by have := p.2; omega)

theorem tupCnt_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : tupCnt (stdT sz hsz) = shapeDeg sz := by
  funext a
  unfold tupCnt shapeDeg
  rw [Finset.card_filter (fun k : Fin K => a.1 < sz k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← card_eq_val (m := sz k) a]
  apply congrArg Finset.card
  ext p
  simp [stdT, Fin.ext_iff]

theorem prod_sz {M : Type*} [CommMonoid M] {K : ℕ} (sz : Fin K → ℕ) (s : Finset (Fin K)) (bnd : ℕ)
    (hb : ∀ k ∈ s, sz k < bnd) (F : ℕ → M) :
    ∏ k ∈ s, F (sz k) = ∏ y ∈ Finset.range bnd, F y ^ (s.filter fun k => sz k = y).card := by
  rw [Finset.prod_comp F sz]
  apply Finset.prod_subset
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact Finset.mem_range.mpr (hb k hk)
  · intro y _ hy
    rw [Finset.mem_image] at hy
    have e : s.filter (fun k => sz k = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk hky
      exact hy ⟨k, hk, hky⟩
    rw [e, Finset.card_empty, pow_zero]

theorem count_succ {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (s : Fin n) :
    (Finset.univ.filter fun k => sz k = s.1 + 1).card = shapeDeg sz s - nuNext (shapeDeg sz) s := by
  unfold nuNext shapeDeg
  split_ifs with h
  · try simp only [Fin.val_mk]
    have hsub : (Finset.univ.filter fun k : Fin K => s.1 + 1 < sz k) ⊆ Finset.univ.filter fun k : Fin K => s.1 < sz k := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
    first
    | rw [← Finset.card_sdiff_of_subset hsub]
    | rw [← Finset.card_sdiff hsub]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  · rw [Nat.sub_zero]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hsz k
    have h2 := s.2
    omega

theorem bidet_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (ν : Fin n → ℕ) (hsh : shapeDeg sz = ν) :
    bideterminant ℤ sz hsz (stdT sz hsz) = hw ℤ (r := n) le_rfl ν := by
  subst hsh
  unfold bideterminant hw
  let F : ℕ → MvPolynomial (Fin n × Fin n) ℤ := fun y => if hy : y ≤ n then lpMinor ℤ y hy hy else 1
  have h1 : ∀ k, initMinor ℤ (stdT sz hsz k) (hsz k) = F (sz k) := by
    intro k
    have e : F (sz k) = lpMinor ℤ (sz k) (hsz k) (hsz k) := dif_pos (hsz k)
    rw [e]
    exact initMinor_std (hsz k) (hsz k)
  simp only [h1]
  rw [prod_sz sz Finset.univ (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) F, Finset.prod_range_succ']
  have h0 : F 0 = 1 := by
    have e : F 0 = lpMinor ℤ 0 (Nat.zero_le n) (Nat.zero_le n) := dif_pos (Nat.zero_le n)
    rw [e]
    simp [lpMinor]
  rw [h0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [count_succ sz hsz s]
  have e : F (s.1 + 1) = lpMinor ℤ (s.1 + 1) (by have := s.2; omega) (by have := s.2; omega) :=
    dif_pos (by have := s.2; omega)
  rw [e]

theorem prod_zsmul' {R : Type*} [CommRing R] {K : ℕ} (a : Fin K → ℤ) (x : Fin K → R) :
    ∏ k, (a k • x k) = (∏ k, a k) • ∏ k, x k := by
  simp only [zsmul_eq_mul, Finset.prod_mul_distrib, Int.cast_prod]

theorem natW_last {n : ℕ} (sg : DomWeight n) (hn : 0 < n) : sg.natW ⟨n - 1, by omega⟩ = 0 := by
  simp [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, hn]

theorem natW_add {n : ℕ} (sg : DomWeight n) (i : Fin n) : ((sg.natW i : ℕ) : ℤ) + sg.detShift = sg.w i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.2
  have hle : sg.detShift ≤ sg.w i := by
    unfold Formalism.BasicNotions.DomWeight.detShift
    rw [dif_pos hn]
    exact sg.anti (Fin.le_iff_val_le_val.mpr (by show i.1 ≤ n - 1; have := i.2; omega))
  simp only [Formalism.BasicNotions.DomWeight.natW]
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
  ring

theorem sz_lt {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (k : Fin K) (hk : 0 < sz k) : sz k < n := by
  have hn : 0 < n := lt_of_lt_of_le hk (hsz k)
  by_contra hcon
  have heq : sz k = n := le_antisymm (hsz k) (not_lt.mp hcon)
  have h1 := congrFun hsh ⟨n - 1, by omega⟩
  rw [natW_last sg hn] at h1
  unfold shapeDeg at h1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ k) (by simp; omega)

theorem lif_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hk : sz k < n) (hm : sz k + 1 ≤ N) :
    lif h (stdT sz hsz k) hm = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk⟩) hm := by
  unfold lif
  congr 1
  funext p
  simp [liftRows, rowsZ, stdT, eRow]
  have hp := p.2
  split_ifs <;> first | rfl | (exfalso; omega)

theorem unl_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hm : sz k ≤ N) : unl h (stdT sz hsz k) hm = lpMinor ℤ (r := N) (n := N) (sz k) hm hm := by
  unfold unl
  exact initMinor_std hm hm

private theorem card_filter_not_mem_sz_eq_succ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) (s : Fin n) :
    (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card =
      if s.1 + 1 = n then 0 else (aa h lam sg s).toNat := by
  unfold Interlace at hI
  unfold GoodL at hL
  have hs0 := s.2
  have e1 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => k ∈ L) =
      Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have e2 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => ¬ k ∈ L) =
      Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have htot : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card +
      (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card =
      (Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).card := by
    rw [← e1, ← e2]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_not _
  have hc := count_succ sz hsz s
  rw [hsh] at hc
  unfold nuNext at hc
  split_ifs with hs
  · rw [dif_neg (show ¬ (s.1 + 1 < n) by omega)] at hc
    have hlast : sg.natW s = 0 := by
      have e : s = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]
      exact natW_last sg (by omega)
    omega
  · have hs' : s.1 + 1 < n := by omega
    have hL1 : s.1 + 1 < N := by omega
    rw [dif_pos hs'] at hc
    have hb : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card =
        (lam.w ⟨s.1 + 1, hL1⟩ - sg.w ⟨s.1 + 1, hs'⟩).toNat := by
      have := hL.2 ⟨s.1 + 1, hs'⟩
      rw [if_neg (show ¬ (((⟨s.1 + 1, hs'⟩ : Fin n) : ℕ) = 0) by simp)] at this
      exact this
    have hI1 : lam.w ⟨s.1 + 1, hL1⟩ ≤ sg.w s := (hI s).2
    have hI2 : sg.w ⟨s.1 + 1, hs'⟩ ≤ lam.w ⟨s.1 + 1, hL1⟩ := (hI ⟨s.1 + 1, hs'⟩).1
    have ha : ((sg.natW s : ℕ) : ℤ) + sg.detShift = sg.w s := natW_add sg s
    have hb2 : ((sg.natW ⟨s.1 + 1, hs'⟩ : ℕ) : ℤ) + sg.detShift = sg.w ⟨s.1 + 1, hs'⟩ := natW_add sg _
    have hX := Int.toNat_of_nonneg (sub_nonneg.mpr hI1)
    have hY := Int.toNat_of_nonneg (sub_nonneg.mpr hI2)
    show _ = (sg.w s - lam.w ⟨s.1 + 1, hL1⟩).toNat
    omega

theorem mlift_std {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hsh : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg := by
  have hL' := hL
  unfold GoodL at hL'
  have hN : ∀ k, sz k + 1 ≤ N := fun k => by have := hsz k; omega
  unfold Mlift xi
  rw [Finset.prod_ite]
  let A : ℕ → MvPolynomial (Fin N × Fin N) ℤ := fun j =>
    if hj : j < n then initMinor ℤ (n := N) (rowsZ h ⟨j, hj⟩) (by show j + 1 ≤ N; omega) else 1
  let B : ℕ → MvPolynomial (Fin N × Fin N) ℤ := fun j =>
    if hj : j ≤ N then lpMinor ℤ (r := N) (n := N) j hj hj else 1
  have hA : ∀ k ∈ Finset.univ.filter (fun k => k ∈ L), lif h (stdT sz hsz k) (hN k) = A (sz k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hk' : sz k < n := sz_lt sg sz hsz hsh k (hL'.1 k hk)
    rw [lif_std h sz hsz k hk' (hN k)]
    have e : A (sz k) = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk'⟩) (hN k) := dif_pos hk'
    rw [e]
  have hB : ∀ k ∈ Finset.univ.filter (fun k => ¬ k ∈ L),
      unl h (stdT sz hsz k) (by have := hsz k; omega) = B (sz k) := by
    intro k _
    have hk' : sz k ≤ N := by have := hsz k; omega
    rw [unl_std h sz hsz k hk']
    have e : B (sz k) = lpMinor ℤ (r := N) (n := N) (sz k) hk' hk' := dif_pos hk'
    rw [e]
  rw [Finset.prod_congr rfl hA, Finset.prod_congr rfl hB]
  rw [prod_sz sz (Finset.univ.filter fun k => k ∈ L) n
    (fun k hk => sz_lt sg sz hsz hsh k (hL'.1 k (by simpa using hk))) A]
  rw [prod_sz sz (Finset.univ.filter fun k => ¬ k ∈ L) (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) B,
    Finset.prod_range_succ']
  have hB0 : B 0 = 1 := by
    have e : B 0 = lpMinor ℤ (r := N) (n := N) 0 (Nat.zero_le N) (Nat.zero_le N) := dif_pos (Nat.zero_le N)
    rw [e]
    simp [lpMinor]
  rw [hB0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
  unfold C0
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi := i.2
  have cL : ((Finset.univ.filter fun k => k ∈ L).filter fun k => sz k = i.1).card =
      if i.1 = 0 then 0 else (bb h lam sg i).toNat := by
    rw [Finset.filter_filter]
    exact hL'.2 i
  have cN : ((Finset.univ.filter fun k => ¬ k ∈ L).filter fun k => sz k = i.1 + 1).card =
      if i.1 + 1 = n then 0 else (aa h lam sg i).toNat := by
    rw [Finset.filter_filter]
    exact card_filter_not_mem_sz_eq_succ h lam sg hI sz hsz hsh L hL i
  have eA : A i.1 = initMinor ℤ (n := N) (rowsZ h i) (by omega) := dif_pos hi
  have eB : B (i.1 + 1) = lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := dif_pos (by omega)
  rw [cL, cN, eA, eB]
  split_ifs <;> ring

theorem top_component_formula : TopPart := by
  intro n N h lam sg hI K sz hsz hsh L hL
  have hext : bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg := by
    rw [bidet_std sz hsz _ hsh]
    unfold extremal
    rfl
  refine ⟨?_, (tupCnt_std sz hsz).trans hsh, hext, mlift_std h lam sg hI sz hsz hsh L hL⟩
  intro J hJ
  by_cases hinj : ∀ k, Function.Injective (J k)
  · have hlt := top_entries sz hsz J hinj (hJ.trans hsh.symm)
    choose σ hσ using top_perm sz hsz J hinj hlt
    refine ⟨∏ k, (Equiv.Perm.sign (σ k) : ℤ), ?_, ?_⟩
    · have e1 : bideterminant ℤ sz hsz J = (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • bideterminant ℤ sz hsz (stdT sz hsz) := by
        unfold bideterminant
        rw [← prod_zsmul']
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [hσ k, initMinor_perm]
      rw [e1, hext]
    · have e2 : Mlift h lam sg sz hsz L J =
          (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • Mlift h lam sg sz hsz L (stdT sz hsz) := by
        unfold Mlift
        rw [← mul_smul_comm, ← prod_zsmul']
        congr 1
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [hσ k]
        split_ifs
        · exact lif_perm h _ _ _
        · exact unl_perm h _ _ _
      rw [e2, mlift_std h lam sg hI sz hsz hsh L hL]
  · obtain ⟨k0, hk0⟩ := not_forall.mp hinj
    refine ⟨0, ?_, ?_⟩
    · rw [zero_smul]
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (initMinor_not_inj _ _ hk0)
    · rw [zero_smul]
      unfold Mlift
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ k0)
      try dsimp only
      split_ifs
      · exact lif_not_inj h _ _ hk0
      · exact unl_not_inj h _ _ hk0

end PI.WGL.LTB
