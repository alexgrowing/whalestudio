import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMXB

namespace Formalism.InvariantFactorPaths.MC

open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.InvariantFactorPaths.OddLevelGainBounds.TB

private lemma neg_logb_norm_natCast_eq_padicValNat (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    -Real.logb p ‖(n : ℚ_[p])‖ = (padicValNat p n : ℝ) := by
  have h0 : ((n : ℚ) : ℚ_[p]) = (n : ℚ_[p]) := by push_cast; rfl
  have h1 : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
    rw [← h0, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
      padicValRat.of_nat]
    push_cast <;> simp [padicValRat.of_nat]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [h1, ← Real.rpow_intCast, Real.logb_rpow (by positivity) hp1.ne']
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg]

private lemma digits_sum_le_sub_one_mul_log_add_one (p : ℕ) [hp : Fact p.Prime] (n Xb : ℕ) (hn : n ≤ Xb) :
    ((p.digits n).sum : ℝ) ≤ ((p : ℝ) - 1) * ((Nat.log p Xb : ℝ) + 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by positivity)
  · have hlen := Nat.digits_len p n hp.out.one_lt hpos.ne'
    have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
      have := List.sum_le_card_nsmul (p.digits n) (p - 1)
        (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp.out.one_lt hx))
      simpa [smul_eq_mul] using this
    rw [hlen] at hsum
    have hlog : Nat.log p n ≤ Nat.log p Xb := Nat.log_mono_right hn
    have h2 : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
      have h3 := (Nat.cast_le (α := ℝ)).mpr hsum
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.out.one_lt.le, Nat.cast_one] at h3
      exact h3
    have hl : (Nat.log p n : ℝ) ≤ Nat.log p Xb := by exact_mod_cast hlog
    nlinarith

lemma per_rowX (p : ℕ) [hp : Fact p.Prime] (Xb S o z e Mm : ℕ) (κ κ4 lgv : ℝ)
    (heo : e ≤ o) (ho : o ≤ Xb) (hS : S ≤ Xb) (hz : z + o ≤ Xb) (hL : (Nat.log p Xb : ℝ) + 1 ≤ lgv)
    (hκ0 : 0 ≤ κ) (hM : Mm = ⌈κ⌉₊) :
    -Real.logb p ‖betaT p Mm z o S e‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ4 ≤
      κ + 3 * lgv + κ4 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hq : 0 < (p : ℝ) - 1 := by linarith
  have hA : p ^ Mm * (e.factorial * (z + e).choose e) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.out.ne_zero)
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne')
  have hB : o.factorial * S.factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hβ : betaT p Mm z o S e = ((p ^ Mm * (e.factorial * (z + e).choose e) : ℕ) : ℚ_[p]) /
      ((o.factorial * S.factorial : ℕ) : ℚ_[p]) := by
    simp only [betaT]; push_cast; ring
  have hA' : ‖((p ^ Mm * (e.factorial * (z + e).choose e) : ℕ) : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast hA)
  have hB' : ‖((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast hB)
  rw [hβ, norm_div, Real.logb_div hA' hB']
  have e1 := neg_logb_norm_natCast_eq_padicValNat p _ hA
  have e2 := neg_logb_norm_natCast_eq_padicValNat p _ hB
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero)
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'),
    padicValNat.prime_pow, padicValNat.mul (Nat.factorial_ne_zero _)
      (Nat.choose_pos (Nat.le_add_left e z)).ne'] at e1
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at e2
  simp only [Nat.cast_add] at e1 e2
  have hC : (padicValNat p ((z + e).choose e) : ℝ) ≤ Nat.log p Xb := by
    have h := @Nat.factorization_choose_le_log p (z + e) e
    rw [Nat.factorization_def _ hp.out] at h
    exact_mod_cast h.trans (Nat.log_mono_right (by omega))
  have L : ∀ n : ℕ, ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = n - ((p.digits n).sum : ℝ) := by
    intro n
    have h := sub_one_mul_padicValNat_factorial (p := p) n
    have h' : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) = ((n - (p.digits n).sum : ℕ) : ℝ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_sub (Nat.digit_sum_le p n), Nat.cast_sub hp.out.one_lt.le] at h'
    simpa using h'
  have dso := digits_sum_le_sub_one_mul_log_add_one p o Xb ho
  have dsS := digits_sum_le_sub_one_mul_log_add_one p S Xb hS
  have dse : (0 : ℝ) ≤ ((p.digits e).sum : ℝ) := by positivity
  have Le := L e
  have Lo := L o
  have LS := L S
  have hsub : ((S + o - e : ℕ) : ℝ) = (S : ℝ) + o - e := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlv : ((p : ℝ) - 1) * ((Nat.log p Xb : ℝ) + 1) ≤ ((p : ℝ) - 1) * lgv :=
    mul_le_mul_of_nonneg_left hL hq.le
  have hdiv : ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) ≤
      2 * lgv - ((padicValNat p e.factorial : ℝ) - padicValNat p o.factorial - padicValNat p S.factorial) := by
    rw [div_le_iff₀ hq, hsub]
    nlinarith
  have hceil : (Mm : ℝ) < κ + 1 := by rw [hM]; exact Nat.ceil_lt_add_one hκ0
  have hL' : (Nat.log p Xb : ℝ) ≤ lgv - 1 := by linarith
  linarith

theorem meanGamX_of (hDeg : GamDeg) (hLead : GamLead) (hC : GamIntC) (hW : Formalism.GM.WindowFullAP) :
    MeanGamX := by
  intro p hp K r hr LLw q J M ρ z w n₀ f ord s d Yw Xb E κ κ4 lgv U V dg hρ hr2 hv hli hspan hord hfil hE hYw hd
    hcop hSs h2S hzo hYX hrX hL hκ hL4 hsmith
  classical
  have hr1 : 1 ≤ r := by omega
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hPolZ : ∀ b, f b ∈ PolZ p r LLw := fun b =>
    Submodule.mem_inf.mpr ⟨hPol b, (Submodule.mem_inf.mp (hmem b)).2⟩
  have hCI := fun x y => hC p K r LLw ρ z (f x) (f y) hr1 hv (hPolZ x) (hPolZ y)
  choose cc hcc using hCI
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set cI := (K + 4) * (r * Nat.log p (S + o + r)) + 6 * Nat.log p (S + o + r) with hcIdef

  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlgv1 : 1 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ0 : 0 ≤ κ := by
    refine le_trans ?_ hκ
    positivity
  have hoS0 : o ≤ S := Finset.single_le_sum (f := LLw.deg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hS2a : S ≤ Xb := by omega
  have ho2a : o ≤ Xb := by omega
  have hcI : (cI : ℝ) ≤ κ := by
    have hX1 : Xb ≠ 0 := by omega
    have hl : Nat.log p (S + o + r) ≤ Nat.log p Xb + 1 := by
      rw [← Nat.log_mul_base hp.out.one_lt hX1]
      apply Nat.log_mono_right
      have : 2 ≤ p := hp.out.two_le
      nlinarith
    have hl' : (Nat.log p (S + o + r) : ℝ) ≤ lgv := by
      have : (Nat.log p (S + o + r) : ℝ) ≤ (Nat.log p Xb : ℝ) + 1 := by exact_mod_cast hl
      linarith
    have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 4) * (r : ℝ) + 6 := by positivity
    calc (cI : ℝ) = (((K : ℝ) + 4) * (r : ℝ) + 6) * (Nat.log p (S + o + r) : ℝ) := by
          rw [hcIdef]; push_cast; ring
      _ ≤ (((K : ℝ) + 4) * (r : ℝ) + 6) * lgv := mul_le_mul_of_nonneg_left hl' hK0
      _ ≤ κ := hκ
  have hcIc : cI ≤ ⌈κ⌉₊ := by
    have : (cI : ℝ) ≤ (⌈κ⌉₊ : ℝ) := hcI.trans (Nat.le_ceil κ)
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + cI = ⌈κ⌉₊ := ⟨⌈κ⌉₊ - cI, Nat.sub_add_cancel hcIc⟩
  obtain ⟨hAeval, hnat, hlead, hord_le, hoS⟩ := lead_part hDeg hLead LLw J M ρ z w n₀ f ord κ4 m cI cc
    hr1 hv hli hspan hord hfil hL4 (fun x y n hn => hcc x y n hn)
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) m cc) with hAqdef
  have hLB := lead_bound p (fun b => ‖betaT p (m + cI) z o S (ord b)‖) (fun b => S + o - ord b) κ4
    (κ + 3 * lgv + κ4) ‖Aq.det.leadingCoeff‖ (fun b => norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) hlead
    (fun b => per_rowX p Xb S o z (ord b) (m + cI) κ κ4 lgv (hord_le b) ho2a hS2a hzo hL hκ0 hm)

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set c' : Fin n₀ → Fin n₀ → ℕ → PadicAlgCl p := fun i j k => alg (coefT p (S + o) m cc i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) (2 * S) c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg (2 * S) _
  have hDk : (binMatK (PadicAlgCl p) (2 * S) c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) (2 * S) c').det
  have hlc : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) (2 * S) c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hprod_pos : 0 < ∏ b, (‖betaT p (m + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ4)) := by
    apply Finset.prod_pos
    intro b _
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos (by linarith) _)
  have hleadne : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm]; exact lt_of_lt_of_le hprod_pos hlead
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) (2 * S) c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * (κ + 3 * lgv + κ4) := by
    rw [hlcnorm, hcard, hnd, hnat]; exact hLB
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap', coefT]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := by
        rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
      have h2 : ((p : ℝ)⁻¹) ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ m * ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 * 1 :=
            mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · simp

  set h := Nat.log p Xb + 1 with hhdef
  have hph : Xb ≤ p ^ h := (Nat.lt_pow_succ_log_self hp.out.one_lt Xb).le
  have hhl : (h : ℝ) ≤ lgv := by rw [hhdef]; push_cast; exact hL
  have hYh : Yw ≤ p ^ h := by omega
  have hdelh : 2 * S ≤ p ^ h := by omega

  set idx : ℤ → ℕ := fun t => ((t - (s : ℤ)) / (d : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (s : ℤ) (d : ℤ) j) = j := by
    intro j
    simp only [hidxdef, progr, add_sub_cancel_left]
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne')]
    simp
  set U' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (U (idx t)).map alg with hU'
  set V' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (V (idx t)).map alg with hV'
  set dg' : ℤ → Fin n₀ → PadicAlgCl p := fun t b => alg (dg (idx t) b) with hdg'
  have hsm : ∀ j ∈ range Yw, (∀ x y, ‖U' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      ‖(U' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧ ‖(V' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) (2 * S) c').map (Polynomial.eval ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p)) =
        U' (progr (s : ℤ) (d : ℤ) j) * Matrix.diagonal (dg' (progr (s : ℤ) (d : ℤ) j)) *
          V' (progr (s : ℤ) (d : ℤ) j) := by
    intro j hj
    obtain ⟨hU1, hV1, hUd, hVd, hfac⟩ := hsmith j (Finset.mem_range.mp hj)
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hU1 x y
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hV1 x y
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hUd
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hVd
    · rw [hAK]
      ext x y
      have hpt : ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p) = ((s + d * j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      have hfe := congrFun (congrFun hfac x) y
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_diagonal] at hfe
      simp only [Matrix.map_apply, hpt, eval_natCast_map, Matrix.mul_apply, Matrix.mul_diagonal]
      rw [hAeval x y (s + d * j) (le_trans hSs (Nat.le_add_right _ _)), hm, hfe, map_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [Matrix.diagonal_apply, map_sum]
  have hcop' : IsCoprime (d : ℤ) (p : ℤ) := hcop
  have hE0 : (0 : ℝ) < E := by linarith
  have key := hW p (PadicAlgCl p) n₀ (2 * S) h E c' (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff
    (binMatK (PadicAlgCl p) (2 * S) c').det.roots (s : ℤ) (d : ℤ) Yw (κ + 3 * lgv + κ4) U' V' dg' hcop'
    (by omega) hYh hdelh hE0 hleadne hc'norm hsplit hsm hLB'

  have hcnt : ∀ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ) ≤
      ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) := by
    intro j _
    have hsub : univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E)) ⊆
        univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp only [hdg', hidx, halg, norm_algebraMap']
      exact hb.le
    exact_mod_cast Finset.card_le_card hsub
  have hYpos : (0 : ℝ) < Yw := by exact_mod_cast hYw
  calc (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw
      ≤ (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) /
          Yw := div_le_div_of_nonneg_right (Finset.sum_le_sum hcnt) hYpos.le
    _ ≤ (n₀ : ℝ) * (((2 * S : ℕ) : ℝ) / Yw + ((κ + 3 * lgv + κ4) + ((2 * S : ℕ) : ℝ) * h / Yw) / E) := key
    _ ≤ n₀ * (2 * (LLw.total : ℝ) / Yw + ((κ + 3 * lgv + κ4) + 2 * (LLw.total : ℝ) * lgv / Yw) / E) := by
      rw [← hSdef]
      push_cast
      have h1 : 2 * (S : ℝ) * h / Yw ≤ 2 * (S : ℝ) * lgv / Yw := by
        apply div_le_div_of_nonneg_right _ hYpos.le
        exact mul_le_mul_of_nonneg_left hhl (by positivity)
      have h2 : (κ + 3 * lgv + κ4) + 2 * (S : ℝ) * h / Yw ≤ (κ + 3 * lgv + κ4) + 2 * (S : ℝ) * lgv / Yw := by
        linarith
      have h3 := div_le_div_of_nonneg_right h2 hE0.le
      have hn0 : (0 : ℝ) ≤ n₀ := by positivity
      nlinarith

end Formalism.InvariantFactorPaths.MC
