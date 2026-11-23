import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumMemLaSet

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumEta (r : ℕ) (Y : ℝ) : ℝ := (1 - 5 / Y) * (1 - 1 / Y) * (1 - (r : ℝ) / (2 * Y))

theorem sum_total_loss (r J N : ℕ) (k Y A : ℝ) (hr : 2 ≤ r) (hk : 5 ≤ k) (hY : 1 ≤ Y) (hJN : J ≤ N) (hN : 1 ≤ N)
    (hA : 1 - 1 / (32 * Y) ≤ A) (hA1 : A ≤ 1) (hlt : 0 < 1 - 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y) :
    0 ≤ 1 - 5 / Y ∧ 0 ≤ 1 - 1 / Y ∧ 0 ≤ 1 - (r : ℝ) / (2 * Y) ∧ 1 - 5 / Y ≤ 1 ∧ 1 - 1 / Y ≤ 1 ∧
      1 - (r : ℝ) / (2 * Y) ≤ 1 ∧
      1 - 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y ≤ A ^ J * sumEta r Y ^ N := by
  have hY0 : 0 < Y := by linarith
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u := 1 / Y with hu
  have hu0 : 0 < u := by positivity
  have e1 : 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y = N * ((r : ℝ) ^ 2 * k * u) := by rw [hu]; ring
  have e5 : 5 / Y = 5 * u := by rw [hu]; ring
  have er : (r : ℝ) / (2 * Y) = (r : ℝ) / 2 * u := by rw [hu]; field_simp
  have e32 : 1 / (32 * Y) = u / 32 := by rw [hu]; field_simp
  rw [e1] at hlt ⊢
  rw [e32] at hA
  unfold sumEta
  rw [e5, er]
  have hrk : 0 ≤ (r : ℝ) ^ 2 * k * u := by positivity
  have h1 : (r : ℝ) ^ 2 * k * u < 1 := by nlinarith
  have hr2k : 10 * (r : ℝ) ≤ (r : ℝ) ^ 2 * k := by nlinarith
  have h5 : 5 * u ≤ 1 := by nlinarith
  have h1u : u ≤ 1 := by nlinarith
  have hru : (r : ℝ) / 2 * u ≤ 1 := by nlinarith
  have hru0 : 0 ≤ (r : ℝ) / 2 * u := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  have hA0 : 0 ≤ A := by nlinarith
  obtain ⟨s1, p1, q1⟩ := sub_le_mul_one_sub_and_mem_unit_interval (P := 1 - 5 * u) (c := u) (s := 1 - 5 * u) (by linarith) (by linarith) hu0.le h1u le_rfl
  obtain ⟨s2, p2, q2⟩ := sub_le_mul_one_sub_and_mem_unit_interval (c := (r : ℝ) / 2 * u) p1 q1 hru0 hru s1
  set η := (1 - 5 * u) * (1 - u) * (1 - (r : ℝ) / 2 * u) with hη
  have hAη : 1 - (7 + (r : ℝ) / 2) * u ≤ A * η := by
    have : (1 - u / 32) * η ≤ A * η := mul_le_mul_of_nonneg_right hA p2
    nlinarith
  have hε : (7 + (r : ℝ) / 2) * u ≤ (r : ℝ) ^ 2 * k * u := by
    apply mul_le_mul_of_nonneg_right _ hu0.le
    nlinarith
  have hbase0 : 0 ≤ 1 - (7 + (r : ℝ) / 2) * u := by linarith
  have hpow : A ^ N ≤ A ^ J := pow_le_pow_of_le_one hA0 hA1 hJN
  have hηN : 0 ≤ η ^ N := pow_nonneg p2 N
  calc 1 - (N : ℝ) * ((r : ℝ) ^ 2 * k * u) ≤ 1 + (N : ℝ) * (-((7 + (r : ℝ) / 2) * u)) := by nlinarith
    _ ≤ (1 + -((7 + (r : ℝ) / 2) * u)) ^ N := one_add_mul_le_pow (by linarith) N
    _ ≤ (A * η) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    _ = A ^ N * η ^ N := mul_pow _ _ _
    _ ≤ A ^ J * η ^ N := mul_le_mul_of_nonneg_right hpow hηN

section Main

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

theorem sum_fac_LL (F : SumFacts X p K) (h5 : 0 ≤ 1 - 5 / X.Y) (h1 : 0 ≤ 1 - 1 / X.Y) (h1' : 1 - 1 / X.Y ≤ 1)
    (hr0 : 0 ≤ 1 - (r : ℝ) / (2 * X.Y)) (hr1 : 1 - (r : ℝ) / (2 * X.Y) ≤ 1) (t : Fin n') (ht : t ∈ X.F.TT) :
    sumEta r X.Y * sumBin r K (X.deg t) ≤ sumBin r K (X.a' p K t) := by
  refine le_trans ?_ (F.compA t ht)
  have hb : 0 ≤ sumBin r K (X.deg t) := zero_le_one.trans (sum_one_le_bin _ _ _)
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hb
  unfold sumEta
  have : (1 - 5 / X.Y) * (1 - 1 / X.Y) ≤ 1 - 5 / X.Y := by nlinarith
  nlinarith [mul_nonneg h5 h1]

theorem sum_fac_fr (F : SumFacts X p K) (hr : 0 < r) (h5 : 0 ≤ 1 - 5 / X.Y) (h1 : 0 ≤ 1 - 1 / X.Y)
    (hr0 : 0 ≤ 1 - (r : ℝ) / (2 * X.Y)) (j : ℤ) (i : Fin r) :
    sumEta r X.Y * sumBin r K (X.deg (posOf n' (X.F.fr j i.val))) ≤
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat) *
        (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) *
        ((X.Pz p K j (X.F.fr j i.val) : ℕ) : ℝ) ^ (r + K - 1) * ((X.Qc p K j : ℕ) : ℝ) ^ K := by
  have ht := (sum_late_mem (F.frlate j i)).2.2.2
  have hA := F.compA _ ht
  have hW := F.compW j i
  set t := posOf n' (X.F.fr j i.val)
  set B := sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  set Qr := ((X.Qc p K j : ℕ) : ℝ)
  set Pr := ((X.Pz p K j (X.F.fr j i.val) : ℕ) : ℝ)
  have hmax : max 0 (1 - (r : ℝ) / (2 * X.Y)) = 1 - (r : ℝ) / (2 * X.Y) := max_eq_right hr0
  have hexp : r + K - 1 = (r - 1) + K := by omega
  have e : B * (Qr ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) * Pr ^ (r + K - 1) * Qr ^ K =
      (1 - (r : ℝ) / (2 * X.Y)) * ((Pr * Qr) ^ (r + K - 1) * B) := by
    rw [hmax, mul_pow, hexp, pow_add Qr]
    ring
  rw [e]
  have hW' : sumBin r K (X.a' p K t) * (1 - 1 / X.Y) ≤ (Pr * Qr) ^ (r + K - 1) * B := by
    have : (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) = Pr * Qr := by push_cast; rfl
    rw [← this]; exact hW
  have h2 : sumBin r K (X.deg t) * (1 - 5 / X.Y) * (1 - 1 / X.Y) ≤ (Pr * Qr) ^ (r + K - 1) * B :=
    (mul_le_mul_of_nonneg_right hA h1).trans hW'
  have h3 := mul_le_mul_of_nonneg_left h2 hr0
  refine le_trans (le_of_eq ?_) h3
  unfold sumEta
  ring

theorem restSum_of (hF : ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → (1088 : ℝ) ≤ X.CLa → (1088 : ℝ) ≤ X.Ck → SumFacts X p K ∧ 1 ≤ X.Ns) : RestSum 1088 1 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk G hG0 hGdep hGsum
  obtain ⟨F, hNs⟩ := hF p n' r K X hX hLa hk
  have hp : 0 < p := hX.prime.pos
  have hr : 0 < r := by have := hX.r2; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hRHS0 : 0 ≤ ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J,
      G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) :=
    Finset.sum_nonneg fun la _ => Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun j _ => hG0 _ _
  have hq0 : (0 : ℝ) < ((p : ℝ) ^ n') ^ (r * K) := by positivity
  rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hq0]
  have hbd : X.bound K 1 = (1 - 1 * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * Dat.k (r := r) K / X.Y) *
      ∏ t ∈ X.F.TT, sumBin r K (X.deg t) := rfl
  have hprod0 : 0 ≤ ∏ t ∈ X.F.TT, sumBin r K (X.deg t) :=
    Finset.prod_nonneg fun t _ => zero_le_one.trans (sum_one_le_bin _ _ _)
  rcases le_or_gt (1 - 1 * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * Dat.k (r := r) K / X.Y) 0 with hb | hb
  · rw [hbd]
    have h1 := mul_nonneg (neg_nonneg.mpr hb) hprod0
    have h2 := mul_nonneg hq0.le hRHS0
    nlinarith

  obtain ⟨hA0l, hA00⟩ := first_sum_factor_bounds hX.Y1 F.a32 hNs
  have hA01 : X.firstSumFactor ≤ 1 := by
    unfold Dat.firstSumFactor
    have : 0 ≤ 1 / X.a ^ (X.Ns ^ 2) := by
      have : 0 ≤ X.a := by have := F.a32; have := hX.Y1; linarith
      positivity
    linarith
  have hJ1 : 1 ≤ X.F.J := hX.valid.1
  have hk5 : (5 : ℝ) ≤ Dat.k (r := r) K := by
    unfold Dat.k
    have := hX.NsK; have := hX.r2
    exact_mod_cast (by omega : 5 ≤ r + K)
  obtain ⟨h5, h1, hr0, -, h1', hr1, htot⟩ := sum_total_loss r X.F.J X.F.TT.card (Dat.k (r := r) K) X.Y X.firstSumFactor hX.r2 hk5 hX.Y1
    F.JN (hJ1.trans F.JN) hA0l hA01 hb

  have hTf0 : ∀ j, 0 ≤ X.sumTf p K j := fun j => by
    unfold Dat.sumTf
    exact pow_nonneg (mul_nonneg (by positivity) (le_max_left _ _)) _
  have hWf0 : ∀ j, 0 ≤ X.sumWf p K j := fun j =>
    Finset.prod_nonneg fun i _ => zero_le_one.trans (sum_one_le_bin _ _ _)
  have hseg0 : ∀ j b, 0 ≤ X.segBound p K j b := fun j b => by
    rw [Dat.sum_segBound_eq]
    exact mul_nonneg (mul_nonneg (mul_nonneg hA00 (hWf0 j)) (hTf0 j))
      (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
  have step1 : ∀ la ∈ X.LA p K, ∏ j : Fin X.F.J, X.segBound p K (j.val : ℤ) (X.nz p K la (j.val : ℤ)) ≤
      ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) := by
    intro la hla
    have e1 : ∀ e : Fin X.F.J → Fin r → ℕ, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) =
        ∏ j : Fin X.F.J, G (j.val : ℤ) (X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j)) :=
      fun e => Finset.prod_congr rfl fun j _ => hGdep _ _ _ (sum_bfam_late la e j)
    rw [Finset.sum_congr rfl fun e _ => e1 e]
    have e2 := Finset.prod_univ_sum (fun j : Fin X.F.J => X.sumTset p K la (j.val : ℤ))
      (fun j ej => G (j.val : ℤ) (X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) ej))
    have e3 : X.EE p K la = Fintype.piFinset (fun j : Fin X.F.J => X.sumTset p K la (j.val : ℤ)) := by
      unfold Dat.EE Dat.sumTset
      congr
    rw [e3, ← e2]
    refine Finset.prod_le_prod (fun j _ => hseg0 _ _) fun j _ => ?_
    exact hGsum (j.val : ℤ) _ (family_degrees_admissible hr hp (fun j x hx => (F.LLsub j x hx).1) la hla _)
      (fun i => X.nz p K la (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum step1) hq0.le)

  have step2 : ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, X.segBound p K (j.val : ℤ) (X.nz p K la (j.val : ℤ)) =
      (∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ))) * ∏ t : Fin n', X.sumSt p K t := by
    rw [← sum_LA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ)),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => Dat.sum_segBound_eq X p K _ _
  rw [step2]

  have step3 : ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
      ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) ≤ ∏ t : Fin n', X.sumSt p K t := by
    have hs := Finset.prod_sdiff (f := fun t => X.sumSt p K t) (Finset.subset_univ X.F.TT)
    rw [← hs, F.tiling]
    have hc : (1 : ℝ) ≤ ∏ t ∈ Finset.univ \ X.F.TT, X.sumSt p K t :=
      sum_one_le_prod _ _ fun t ht => sum_St_nontop t (Finset.mem_sdiff.mp ht).2
    have hm : ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
        ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) ≤
        ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), X.sumSt p K (posOf n' x) := by
      refine Finset.prod_le_prod (fun j _ => mul_nonneg
        (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
        (Finset.prod_nonneg fun i _ => by positivity)) fun j hj => ?_
      rw [F.split (j : ℤ) (fun x => X.sumSt p K (posOf n' x))]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => by positivity)
        (Finset.prod_nonneg fun x _ => sum_St_nonneg _)
      · exact Finset.prod_le_prod (fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _)) fun x hx =>
          sum_St_LL F hr hp ⟨j, Finset.mem_range.mp hj⟩ hx
      · exact Finset.prod_le_prod (fun i _ => by positivity) fun i _ => sum_St_fr F hr hp (j : ℤ) i
    have hnn : 0 ≤ ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), X.sumSt p K (posOf n' x) :=
      Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun x _ => sum_St_nonneg _
    nlinarith
  have hC0 : 0 ≤ ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ)) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (mul_nonneg hA00 (hWf0 _)) (hTf0 _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step3 hC0) hq0.le)

  have hW : ∏ j ∈ Finset.range X.F.J, X.sumWf p K (j : ℤ) = ∏ j ∈ Finset.range X.F.J, X.sumWf p K ((j : ℤ) + 1) :=
    (prod_range_shift_of_periodic (fun j => X.sumWf p K j) X.F.J hJ1 (fun j => by
      unfold Dat.sumWf
      exact Finset.prod_congr rfl fun i _ => by rw [F.perW j i])).symm
  have hQ : ((p : ℝ) ^ n') ^ (r * K) = ∏ j ∈ Finset.range X.F.J, (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r := by
    have := F.prodQ
    have h' : (p : ℝ) ^ n' = ∏ j ∈ Finset.range X.F.J, ((X.Qc p K (j : ℤ) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← this]; push_cast; rfl
    rw [h', ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have regroup : ((p : ℝ) ^ n') ^ (r * K) * ((∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ))) *
      ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
      ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1))) =
      ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
        (X.sumWf p K ((j : ℤ) + 1) * X.sumTf p K (j : ℤ) *
          (∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) *
          (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r))) := by
    rw [hQ]
    simp only [Finset.prod_mul_distrib]
    rw [hW]
    ring
  rw [regroup, hbd]
  refine le_trans (mul_le_mul_of_nonneg_right htot hprod0) ?_
  have hfin : X.firstSumFactor ^ X.F.J * sumEta r X.Y ^ X.F.TT.card * ∏ t ∈ X.F.TT, sumBin r K (X.deg t) =
      ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * ∏ x ∈ X.toLate (j : ℤ), (sumEta r X.Y * sumBin r K (X.deg (posOf n' x)))) := by
    rw [Finset.prod_mul_distrib, ← F.tiling (fun t => sumEta r X.Y * sumBin r K (X.deg t)), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, Finset.card_range]
    ring
  rw [hfin]
  have heta0 : 0 ≤ sumEta r X.Y := mul_nonneg (mul_nonneg h5 h1) hr0
  refine Finset.prod_le_prod (fun j _ => mul_nonneg hA00 (Finset.prod_nonneg fun x _ =>
    mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _)))) fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ hA00
  rw [F.split (j : ℤ) (fun x => sumEta r X.Y * sumBin r K (X.deg (posOf n' x)))]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _)))
    (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
  · exact Finset.prod_le_prod (fun x _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _))) fun x hx =>
      sum_fac_LL F h5 h1 h1' hr0 hr1 _ (sum_late_mem (F.LLsub _ _ hx).1).2.2.2
  · have e : X.sumWf p K ((j : ℤ) + 1) * X.sumTf p K (j : ℤ) *
        (∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) *
        (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r =
        ∏ i : Fin r, (sumBin r K ((X.Bw p K ((j : ℤ) + 1) (X.F.fr (j : ℤ) i.val) - (X.m0 K : ℤ)).toNat) *
          (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) *
          ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1) * ((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      unfold Dat.sumWf Dat.sumTf
      simp only [add_sub_cancel_right, mul_pow]
    rw [e]
    exact Finset.prod_le_prod (fun i _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _))) fun i _ =>
      sum_fac_fr F hr h5 h1 hr0 (j : ℤ) i

end Main

end Formalism.MainNotions.SelectionLemmas.Pf
