import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section SchForm

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem phi_Wm_last_of_sch (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by
  classical
  rw [phi_apply_eq, ← (Fin.snocEquiv (fun _ => Fin n × Fin n)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_eq_zero (fun init _ => ?_)
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hem | ⟨⟨p₀⟩⟩
  · simp [Finset.univ_eq_empty]
  · have h0 := hSch _ (hF (Fin.snoc init p₀))
    rw [sch_phi_one_apply] at h0
    simp only [sch_slice_apply, Fin.update_snoc_last] at h0
    have hs : ∀ x : Fin n × Fin n, (Fin.snocEquiv (fun _ => Fin n × Fin n)) (x, init) = Fin.snoc init x :=
      fun x => rfl
    simp only [hs, sch_word_snoc, Module.End.mul_apply, ← map_sum]
    rw [show (∑ x : Fin n × Fin n, (E x.1 x.2) (F (Fin.snoc init x))) = 0 from h0, map_zero]

theorem phi_Wm_position_of_sch (hE : IsGlRep E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M}
    (hF0 : F ∈ ncV ε V (k + 1)) (hF : ∀ κ, slice i κ F ∈ Wm ε E V) :
    phi E (k + 1) F ∈ layer ε E V k := by
  have hsub := phi_permute_sub_mem hE hV.2.1 (Equiv.swap i (Fin.last k)) hF0
  have hzero : phi E (k + 1) (permute (Equiv.swap i (Fin.last k)) F) = 0 := by
    apply phi_Wm_last_of_sch hSch
    intro κ
    have hs : slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) =
        slice i (κ ∘ Equiv.swap i (Fin.last k)) F := by
      apply big_ext
      intro ι
      rw [sch_slice_apply, sch_slice_apply, sch_permute_apply, Function.update_comp_equiv,
        Equiv.symm_swap, Equiv.swap_apply_right]
    rw [hs]
    exact hF _
  rw [hzero, sub_zero] at hsub
  exact hsub

private theorem sum_pairs_sub_eq_sum_mul_count_diff (P : Fin n → Fin n → Prop) [DecidableRel P]
    (hP : ∀ c d, P c d ↔ P d c) (ν : Fin n → ℝ) :
    ∑ c, ∑ d, (if c < d ∧ P c d then ν c - ν d else 0) =
      ∑ c, ν c * ((∑ d, if c < d ∧ P c d then (1 : ℝ) else 0) -
        ∑ d, if d < c ∧ P c d then (1 : ℝ) else 0) := by
  have h1 : ∀ c d, (if c < d ∧ P c d then ν c - ν d else 0) =
      (if c < d ∧ P c d then ν c else 0) - (if c < d ∧ P c d then ν d else 0) := by
    intro c d
    split_ifs <;> ring
  simp only [h1, Finset.sum_sub_distrib]
  have h2 : ∑ c, ∑ d, (if c < d ∧ P c d then ν d else 0) =
      ∑ c, ∑ d, (if d < c ∧ P c d then ν c else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    by_cases hdc : d < c
    · by_cases hp : P c d
      · rw [if_pos ⟨hdc, (hP c d).mp hp⟩, if_pos ⟨hdc, hp⟩]
      · rw [if_neg (fun h => hp ((hP c d).mpr h.2)), if_neg (fun h => hp h.2)]
    · rw [if_neg (fun h => hdc h.1), if_neg (fun h => hdc h.1)]
  rw [h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl (fun d _ => ?_) <;> split_ifs <;> ring

private theorem sum_pairs_eq_casValK (μ : Fin n → ℝ) :
    ∑ a, ∑ b, ((if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a - μ b else 0)) =
      casValK ε μ := by
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_pairs_sub_eq_sum_mul_count_diff (fun c d => ε d = ε c) (fun c d => eq_comm) μ]
  simp only [casValK, nsq, dot, Pi.add_apply, rhoC, numRho_cardR]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

private theorem casimirK_apply_isKHWVec_of_isGlRep {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X}
    (hw : IsKHWVec ε A μ w) : casimirK ε A w = (casValK ε μ : ℂ) • w := by
  have hterm : ∀ a b, (if ε b = ε a then A a b (A b a w) else 0) =
      (((if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a - μ b else 0) : ℝ) : ℂ) • w := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · by_cases hab : ε b = ε a
      · have hc := congrArg (fun T : Module.End ℂ X => T w) (hA a b b a)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true] at hc
        rw [hw.2 a b h hab.symm, map_zero, sub_zero, hw.1 a, hw.1 b] at hc
        rw [if_pos hab, hc, if_neg (ne_of_lt h), if_pos ⟨h, hab⟩]
        simp [sub_smul]
      · rw [if_neg hab, if_neg (ne_of_lt h), if_neg (fun h' => hab h'.2)]
        simp
    · rw [if_pos rfl, hw.1 a, map_smul, hw.1 a, smul_smul]
      simp [sq]
    · by_cases hab : ε b = ε a
      · rw [if_pos hab, hw.2 b a h hab, map_zero, if_neg (ne_of_gt h),
          if_neg (fun h' => (lt_asymm h) h'.1)]
        simp
      · rw [if_neg hab, if_neg (ne_of_gt h), if_neg (fun h' => hab h'.2)]
        simp
  have hsum : casimirK ε A w = ∑ a, ∑ b, (if ε b = ε a then A a b (A b a w) else 0) := by
    simp only [casimirK, LinearMap.sum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    split_ifs <;> simp
  rw [hsum]
  simp only [hterm, ← Finset.sum_smul]
  congr 1
  rw [← sum_pairs_eq_casValK μ]
  push_cast
  rfl

theorem khw_layer_succ_bound_of_sch (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) (k : ℕ) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ layer ε E V (k + 1)) (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0)
    (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) :
    IsNCSum ε (k + 1) (μ - lowK ε lam) ∧
      casValK ε (lowK ε lam) + 2 * ((k : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨P, hPm, hP0, hPk, hPperp⟩ := lift_layer hE hU hV.1 hV.2.1 hw hperp hμ hw0
  have hposition : ∀ i κ, slice i κ P ∈ Wp ε E V := by
    intro i
    exact position_perp hE hU hV hmono hh hbig i hPm
      (fun F hF hsl => hPperp F hF (phi_Wm_position_of_sch hE hV hSch i hF hsl))
  have hB := bochner_ineq hE hU hV hmono hh hbig hPm hposition
  have hre : RCLike.re (inner ℂ ((casValK ε μ : ℂ) • P) P) = casValK ε μ * ‖P‖ ^ 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [casimirK_apply_isKHWVec_of_isGlRep (bAct_isGlRep hE (k + 1)) hPk, hre] at hB
  have hpos : 0 < ‖P‖ ^ 2 := pow_pos (norm_pos_iff.mpr hP0) 2
  refine ⟨khw_big_weight hE hV hPm hP0 hPk, ?_⟩
  have h2 := le_of_mul_le_mul_right hB hpos
  push_cast at h2
  linarith

theorem highest_weight_decomposition_of_gap (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ m, ∃ ws : Fin m → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin m, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧ (ws j ≠ 0 →
        IsNCSum ε ((j : ℕ) + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
        casValK ε (lowK ε lam) + 2 * (((j : ℕ) : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ) := by
  obtain ⟨m, hwm⟩ := exists_layer_of_mem_genSub hE hV.2.1 hw
  obtain ⟨w₀, hw₀, hkw₀, ws, hwe, hws⟩ := layer_khw_decomp hE hU hV.1 hV.2.1 hwm hμ
  refine ⟨w₀, hw₀, hkw₀, m, ws, hwe, fun j => ⟨(hws j).1, fun hne => ?_⟩⟩
  obtain ⟨hmem, hperp, hkhw⟩ := hws j
  obtain ⟨hnc, hle⟩ :=
    khw_layer_succ_bound_of_sch hE hU hV hSch hmono hh hbig (j : ℕ) hmem hperp hne hkhw
  refine ⟨hnc, ?_, hle⟩
  obtain ⟨a, b, hab⟩ := isNCSum_succ_exists hnc
  have := (gap_gt hab hbig).2
  linarith

theorem khw_lowK_mem_of_sch (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hSch : ∀ x ∈ Wm ε E V, phi E 1 x = 0)
    (hgap : StdGap ε lam) {w : M} (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E (lowK ε lam) w) :
    w ∈ V := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨w₀, hw₀, -, m, ws, hwe, hws⟩ := highest_weight_decomposition_of_gap hE hU hV hSch hmono hh hbig hw hμ
  have hz : ∀ j, ws j = 0 := by
    intro j
    by_contra hne
    obtain ⟨-, hpos, hle⟩ := (hws j).2 hne
    have : 0 < 2 * (((j : ℕ) : ℝ) + 1) * (h - n + 1) := by positivity
    linarith
  rw [hwe, Finset.sum_eq_zero (fun j _ => hz j), add_zero]
  exact hw₀

theorem exists_khw_of_not_sch (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hne : ∃ x ∈ Wm ε E V, phi E 1 x ≠ 0) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧
      ∃ w ∈ layer ε E V 1, w ≠ 0 ∧ IsKHWVec ε E (lowK ε lam - root a b) w := by
  classical
  obtain ⟨x₀, hx₀, hphi⟩ := hne
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  have : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hTst : IsKStableSub ε E ((Wm ε E V).map (phi E 1)) := by
    intro a b hab v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr
      ⟨bAct E 1 a b x, Wm_kStable hE hU hV a b hab x hx, phi_bAct hE 1 hab x⟩
  have hTne : (Wm ε E V).map (phi E 1) ≠ ⊥ := by
    intro hbot
    have hm := Submodule.mem_map_of_mem (f := phi E 1) hx₀
    rw [hbot] at hm
    exact hphi ((Submodule.mem_bot ℂ).mp hm)
  obtain ⟨w, hwT, hw0, μ, hkμ⟩ := exists_khw hE hKU inferInstance hTst hTne
  obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hwT
  obtain ⟨x, hx, -, hkx, hfx⟩ := lift_khw (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab y => phi_bAct hE 1 hab y) hfdW (Wm_kStable hE hU hV) hx₁ hkμ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hw0
    rw [← hfx, h0, map_zero]
  obtain ⟨a, b, hab, hε, hμe⟩ := Wm_khw hE hU hV hmono hh hbig hx hx0 hkx
  refine ⟨a, b, hab, hε, phi E 1 x₁, ?_, hw0, hμe ▸ hkμ⟩
  rw [← hfx]
  exact phi_mem_layer (Wm_le_ncV hx)

theorem sch_of_no (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0) :
    ∀ x ∈ Wm ε E V, phi E 1 x = 0 := by
  intro x hx
  by_contra hne
  obtain ⟨a, b, hab, hε, w, hw, hw0, hkhw⟩ :=
    exists_khw_of_not_sch hE hU hV hmono hh hbig ⟨x, hx, hne⟩
  exact hw0 (hNo a b hab hε w hw hkhw)

private theorem sum_opposite_sign_pairs_eq_neg_two_dot_rhoN (ν : Fin n → ℝ) :
    ∑ c, ∑ d, (if d < c ∧ ε d ≠ ε c then ν c - ν d else 0) = -(2 * dot ν (rhoN ε)) := by
  have hsw : ∑ c, ∑ d, (if d < c ∧ ε d ≠ ε c then ν c - ν d else 0) =
      -(∑ c, ∑ d, (if c < d ∧ ε d ≠ ε c then ν c - ν d else 0)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases h1 : c < d
    · by_cases h2 : ε d = ε c
      · rw [if_neg (fun h => h.2 h2.symm), if_neg (fun h => h.2 h2), neg_zero]
      · rw [if_pos ⟨h1, fun h => h2 h.symm⟩, if_pos ⟨h1, h2⟩]
        ring
    · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1), neg_zero]
  rw [hsw, sum_pairs_sub_eq_sum_mul_count_diff (fun c d => ε d ≠ ε c)
    (fun c d => ⟨fun h e => h e.symm, fun h e => h e.symm⟩) ν]
  simp only [dot, rhoN, numRho_cardR, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring

private theorem rho_eq_rhoC_add_rhoN' (ε : Fin n → Bool) (c : Fin n) : rho n c = rhoC ε c + rhoN ε c := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun d : Fin n => c < d)) (fun d => ε d = ε c)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun d : Fin n => d < c)) (fun d => ε d = ε c)
  simp only [Finset.filter_filter] at h1 h2
  have h3 : (Finset.univ.filter (fun d : Fin n => c < d)).card = n - 1 - c := by
    rw [← Fin.card_Ioi]
    congr 1
    ext d
    simp
  have h4 : (Finset.univ.filter (fun d : Fin n => d < c)).card = c := by
    rw [← Fin.card_Iio]
    congr 1
    ext d
    simp
  rw [h3] at h1
  rw [h4] at h2
  have hc : (c : ℕ) < n := c.2
  have e1 : ((n - 1 - (c : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - c := by
    rw [Nat.cast_sub (by omega : (c : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    simp
  have h1' := congrArg (Nat.cast : ℕ → ℝ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  rw [e1] at h1'
  push_cast at h1' h2'
  simp only [rho, rhoC, rhoN, ne_eq]
  linarith

theorem no_of_casimir (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap : StdGap ε lam) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  classical
  intro a b hab hε w hw hkhw
  by_contra hw0
  have hcas : casimir E w = (casVal lam : ℂ) • w := casimir_genSub hE hc w (layer_le_genSub 1 hw)
  set ν := lowK ε lam - root a b with hνdef
  have hsm : ∀ r : ℝ, RCLike.re (inner ℂ ((r : ℂ) • w) w) = r * ‖w‖ ^ 2 := by
    intro r
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hneg : ∀ c d, ε c ≠ ε d → RCLike.re (inner ℂ (E c d (E d c w)) w) = -‖E d c w‖ ^ 2 := by
    intro c d hcd
    rw [hU c d, adjSign, if_neg hcd, neg_one_mul, map_neg, inner_self_eq_norm_sq]
  have hcomm : ∀ c d, E c d (E d c w) = E d c (E c d w) + ((ν c - ν d : ℝ) : ℂ) • w := by
    intro c d
    have h := congrArg (fun T : Module.End ℂ M => T w) (hE c d d c)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true] at h
    rw [hkhw.1 c, hkhw.1 d] at h
    rw [Complex.ofReal_sub, sub_smul, ← h]
    abel
  have hbd : ∀ c d, RCLike.re (inner ℂ (E c d (E d c w)) w) ≤
      ((if c = d then ν c ^ 2 else 0) + (if c < d ∧ ε d = ε c then ν c - ν d else 0) +
        (if d < c ∧ ε d ≠ ε c then ν c - ν d else 0)) * ‖w‖ ^ 2 := by
    intro c d
    rcases lt_trichotomy c d with hcd | rfl | hcd
    · by_cases hs : ε d = ε c
      · rw [hcomm c d, hkhw.2 c d hcd hs.symm, map_zero, zero_add, hsm,
          if_neg (ne_of_lt hcd), if_pos ⟨hcd, hs⟩, if_neg (fun h => lt_asymm hcd h.1)]
        simp
      · rw [hneg c d (fun h => hs h.symm), if_neg (ne_of_lt hcd), if_neg (fun h => hs h.2),
          if_neg (fun h => lt_asymm hcd h.1)]
        have := sq_nonneg ‖E d c w‖
        simp only [add_zero, zero_mul]
        linarith
    · rw [hkhw.1 c, map_smul, hkhw.1 c, smul_smul, if_pos rfl,
        if_neg (fun h => lt_irrefl c h.1), if_neg (fun h => lt_irrefl c h.1), ← Complex.ofReal_mul, hsm]
      simp [sq]
    · by_cases hs : ε d = ε c
      · rw [hkhw.2 d c hcd hs, map_zero, inner_zero_left, map_zero, if_neg (ne_of_gt hcd),
          if_neg (fun h => lt_asymm hcd h.1), if_neg (fun h => h.2 hs)]
        simp
      · rw [hcomm c d, inner_add_left, map_add, hneg d c hs, hsm, if_neg (ne_of_gt hcd),
          if_neg (fun h => lt_asymm hcd h.1), if_pos ⟨hcd, hs⟩]
        have := sq_nonneg ‖E c d w‖
        simp only [zero_add]
        linarith
  have hsumre : RCLike.re (inner ℂ (casimir E w) w) =
      ∑ c, ∑ d, RCLike.re (inner ℂ (E c d (E d c w)) w) := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, map_sum]
  have hT : ∑ c, ∑ d, ((if c = d then ν c ^ 2 else 0) + (if c < d ∧ ε d = ε c then ν c - ν d else 0) +
      (if d < c ∧ ε d ≠ ε c then ν c - ν d else 0)) = casValK ε ν - 2 * dot ν (rhoN ε) := by
    rw [← sum_pairs_eq_casValK ν, sub_eq_add_neg, ← sum_opposite_sign_pairs_eq_neg_two_dot_rhoN ν]
    simp only [Finset.sum_add_distrib]
  have hle : casVal lam * ‖w‖ ^ 2 ≤ (casValK ε ν - 2 * dot ν (rhoN ε)) * ‖w‖ ^ 2 := by
    rw [← hsm, ← hcas, hsumre, ← hT, Finset.sum_mul]
    refine Finset.sum_le_sum (fun c _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun d _ => hbd c d)
  have hpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw0) 2
  have hle' := le_of_mul_le_mul_right hle hpos
  have hgapab := sch_gap hgap hab hε
  have hnum : casValK ε ν - 2 * dot ν (rhoN ε) - casVal lam =
      nsq (root a b) - 2 * dot lam (root a b) + 4 * dot (rhoC ε) (rhoN ε) := by
    simp only [casValK, casVal, nsq, dot, hνdef, lowK, Pi.add_apply, Pi.sub_apply, rho_eq_rhoC_add_rhoN' ε]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [nsq_root (ne_of_lt hab)] at hnum
  linarith

theorem khw_lowK_mem_of_no (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0)
    (hgap : StdGap ε lam) {w : M} (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E (lowK ε lam) w) :
    w ∈ V := by
  obtain ⟨hmono, h, hh, hbig⟩ := id hgap
  exact khw_lowK_mem_of_sch hE hU hV (sch_of_no hE hU hV hmono hh hbig hNo) hgap hw hμ

end SchForm

end ReciprocityTheory.ChartRestriction.DS
