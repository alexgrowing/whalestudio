import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace ZeroPointGroupLaw

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence

variable {C : Type} [Field C] [CharZero C] {V : VF C} {dd : ℕ}

theorem eval_identity_point (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ev
  have e : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = MvPowerSeries.X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem constant_zero_first_then_zero : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k <;> simp [pt]

theorem integral_first_zero_points : ∀ k i, IntS V ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) k i) := by
  intro k i
  fin_cases k
  · exact intS_X _
  · exact intS_zero

theorem constant_zero_zero_first : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k <;> simp [pt]

theorem constant_zero_singleton {a : Pt C 2 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : Z0 (![a] : Fin 1 → Pt C 2 dd) := by
  intro k i
  fin_cases k
  simpa using ha i

theorem group_law_zero_right_one (G : FGLaw C dd) (i : Fin dd) :
    ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (G.F i) = pt C dd 0 i := by
  conv_lhs => rw [← G.comm i]
  rw [ev_ev (z0_pp 1 0) constant_zero_first_then_zero]
  have e1 : (fun k j => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
      ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) = ![0, pt C dd 0] := by
    funext k j
    fin_cases k
    · exact ev_X constant_zero_first_then_zero 1 j
    · exact ev_X constant_zero_first_then_zero 0 j
  rw [e1]
  exact G.unit i

theorem const_dF (G : FGLaw C dd) (i j : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C ((1 : Fin 2), j) (G.F i)) = if j = i then 1 else 0 := by
  have h := congrArg (fun f => MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C ((0 : Fin 1), j) f)) (G.unit i)
  simp only [pderiv_eval_pair constant_zero_zero_first] at h
  have e0 : ∀ r, MvPowerSeries.pderiv C ((0 : Fin 1), j) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) 0 r) = 0 :=
    fun r => by simp
  have e1 : ∀ r, MvPowerSeries.pderiv C ((0 : Fin 1), j) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) 1 r) =
      if r = j then 1 else 0 := fun r => by
    show MvPowerSeries.pderiv C ((0 : Fin 1), j) (MvPowerSeries.X ((0 : Fin 1), r)) = _
    split_ifs with hr
    · subst hr
      exact MvPowerSeries.pderiv_X_self
    · exact MvPowerSeries.pderiv_X_of_ne (fun h' => hr (Prod.ext_iff.1 h').2)
  simp only [e0, e1, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, constantCoeff_ev constant_zero_zero_first] at h
  rw [h]
  by_cases hji : j = i
  · subst hji
    simp
  · rw [if_neg hji, MvPowerSeries.pderiv_X_of_ne (fun h' => hji (Prod.ext_iff.1 h').2.symm), map_zero]

theorem pderiv_eval_single {n : ℕ} (a : Pt C n dd) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : PS C 1 dd)
    (q : Fin n × Fin dd) :
    MvPowerSeries.pderiv C q (ev (n := n) ![a] f) =
      ∑ r, ev (n := n) ![a] (MvPowerSeries.pderiv C ((0 : Fin 1), r) f) * MvPowerSeries.pderiv C q (a r) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => (![a] : Fin 1 → Pt C n dd) p.1 p.2)
    (fun p => (z0_1 a ha) p.1 p.2) f q, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem hadd (G : FGLaw C dd) : addOf G.F (pt C dd 0) (pt C dd 1) = G.F := by
  funext j
  exact eval_points_two (G.F j)

theorem E_D_cobd (G : FGLaw C dd) (A : PS C 1 dd) (j : Fin dd) :
    ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) (cobd G.F A)) =
      ∑ r, MvPowerSeries.pderiv C ((0 : Fin 1), r) A *
          ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) (G.F r)) -
        ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
          (ev (n := 2) ![pt C dd 1] (MvPowerSeries.pderiv C ((0 : Fin 1), j) A)) := by
  unfold cobd
  rw [hadd G, map_sub, map_sub, pderiv_eval_single G.F G.const, pderiv_eval_single (pt C dd 0) (z0_pt 0),
    pderiv_eval_single (pt C dd 1) (z0_pt 1)]
  have e0 : ∀ r, MvPowerSeries.pderiv C ((1 : Fin 2), j) (pt C (n := 2) dd 0 r) = 0 := fun r =>
    MvPowerSeries.pderiv_X_of_ne (fun h' => by simp at h')
  have e1 : ∀ r, MvPowerSeries.pderiv C ((1 : Fin 2), j) (pt C (n := 2) dd 1 r) = if r = j then 1 else 0 := by
    intro r
    show MvPowerSeries.pderiv C ((1 : Fin 2), j) (MvPowerSeries.X ((1 : Fin 2), r)) = _
    split_ifs with hr
    · subst hr
      exact MvPowerSeries.pderiv_X_self
    · exact MvPowerSeries.pderiv_X_of_ne (fun h' => hr (Prod.ext_iff.1 h').2)
  simp only [e0, e1, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [ev_sub constant_zero_first_then_zero, ev_sum constant_zero_first_then_zero]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ev_mul constant_zero_first_then_zero, ev_ev (z0_1 _ G.const) constant_zero_first_then_zero]
  have e2 : (fun k i => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![G.F] : Fin 1 → Pt C 2 dd) k i)) =
      ![pt C dd 0] := by
    funext k i
    fin_cases k
    exact group_law_zero_right_one G i
  rw [e2, eval_identity_point]

theorem maximal_eval_second_constant {g : PS C 1 dd} (hg : V.MM (MvPowerSeries.constantCoeff g)) :
    MMS V (ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] g)) := by
  rw [ev_ev (z0_1 _ (z0_pt 1)) constant_zero_first_then_zero]
  have e : (fun k i => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![pt C dd 1] : Fin 1 → Pt C 2 dd) k i)) =
      fun _ _ => 0 := by
    funext k i
    fin_cases k
    exact ev_X constant_zero_first_then_zero 1 i
  rw [e]
  unfold ev
  rw [show (fun p : Fin 1 × Fin dd => (fun (_ : Fin 1) (_ : Fin dd) => (0 : PS C 1 dd)) p.1 p.2) =
    (0 : Fin 1 × Fin dd → PS C 1 dd) from rfl, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  intro μ
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C]
  split_ifs
  · simpa using hg
  · simpa using (mm_zero : V.MM (0 : C))

theorem mms_pderiv_frobTw {σ : Type} {c : MvPowerSeries σ C} (hc : IntS V c) (s : σ) :
    MMS V (MvPowerSeries.pderiv C s (frobTw V.l c)) := by
  intro μ
  rw [MvPowerSeries.coeff_pderiv, coeff_frobTw]
  split_ifs with h
  · have hs := h s
    rw [Finsupp.add_apply, Finsupp.single_eq_same] at hs
    have : ((μ s : C) + 1) = ((μ s + 1 : ℕ) : C) := by push_cast; ring
    rw [this]
    exact mm_mul_ge' (VF.Ge.pow (hc _) _) (mm_natCast_of_dvd hs)
  · rw [zero_mul]
    exact mm_zero

variable (G : FGLaw C dd) {A : PS C 1 dd} {c : PS C 2 dd}

theorem mms_dA_M (hc : IntS V c) (hlin : ∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A))
    (hfe : ∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) (j : Fin dd) :
    MMS V (∑ r, MvPowerSeries.pderiv C ((0 : Fin 1), r) A *
      ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) (G.F r))) := by
  have h1 : MMS V (ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
      (MvPowerSeries.pderiv C ((1 : Fin 2), j) (cobd G.F A - frobTw V.l c))) :=
    MMS.ev_of constant_zero_first_then_zero integral_first_zero_points ((show MMS V (cobd G.F A - frobTw V.l c) from hfe).pderiv _)
  have h2 : MMS V (ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
      (MvPowerSeries.pderiv C ((1 : Fin 2), j) (frobTw V.l c))) :=
    MMS.ev_of constant_zero_first_then_zero integral_first_zero_points (mms_pderiv_frobTw hc _)
  have hcst : V.MM (MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C ((0 : Fin 1), j) A)) := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add]
    simpa using hlin j
  have h3 := maximal_eval_second_constant (dd := dd) hcst
  rw [map_sub, ev_sub constant_zero_first_then_zero, E_D_cobd] at h1
  have e : ∀ (S X Y : PS C 1 dd), S = (S - X - Y) + Y + X := fun S X Y => by ring
  rw [e (∑ r, _) _ _]
  exact (h1.add h2).add h3

theorem mms_dA (hF : ∀ i, IntS V (G.F i)) (hc : IntS V c) (hlin : ∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A))
    (hfe : ∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) (i : Fin dd) :
    MMS V (MvPowerSeries.pderiv C ((0 : Fin 1), i) A) := by
  set M : Fin dd → Fin dd → PS C 1 dd := fun j r =>
    ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (MvPowerSeries.pderiv C ((1 : Fin 2), j) (G.F r)) with hMdef
  have hM : ∀ j, MMS V (∑ r, MvPowerSeries.pderiv C ((0 : Fin 1), r) A * M j r) :=
    fun j => mms_dA_M G hc hlin hfe j
  have hMint : ∀ j r, IntS V (M j r) := fun j r =>
    intS_ev constant_zero_first_then_zero integral_first_zero_points (intS_pderiv (hF r) _)
  have hMc : ∀ j r, MvPowerSeries.constantCoeff (M j r) = if j = r then 1 else 0 := fun j r => by
    rw [hMdef]
    simp only
    rw [constantCoeff_ev constant_zero_first_then_zero, const_dF G r j]
  suffices h : ∀ n, ∀ ν : Fin 1 × Fin dd →₀ ℕ, ν.degree = n → ∀ i,
      V.MM (MvPowerSeries.coeff ν (MvPowerSeries.pderiv C ((0 : Fin 1), i) A)) from
    fun ν => h _ ν rfl i
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ν hν i
    have h := hM i ν
    rw [map_sum] at h
    have hsplit : ∀ r, MvPowerSeries.coeff ν (MvPowerSeries.pderiv C ((0 : Fin 1), r) A * M i r) =
        MvPowerSeries.coeff ν (MvPowerSeries.pderiv C ((0 : Fin 1), r) A) * MvPowerSeries.constantCoeff (M i r) +
          ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal ν).erase (ν, 0),
            MvPowerSeries.coeff p.1 (MvPowerSeries.pderiv C ((0 : Fin 1), r) A) * MvPowerSeries.coeff p.2 (M i r) := by
      intro r
      rw [MvPowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ (show ((ν, 0) : (Fin 1 × Fin dd →₀ ℕ) × (Fin 1 × Fin dd →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal ν from
          Finset.HasAntidiagonal.mem_antidiagonal.2 (add_zero ν)),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hrest : ∀ r, V.MM (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal ν).erase (ν, 0),
        MvPowerSeries.coeff p.1 (MvPowerSeries.pderiv C ((0 : Fin 1), r) A) * MvPowerSeries.coeff p.2 (M i r)) := by
      intro r
      refine mm_sum _ _ fun p hp => ?_
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      have h2 : p.2 ≠ 0 := by
        intro h0
        apply hne
        rw [h0, add_zero] at hmem
        ext <;> simp [hmem, h0]
      have hdeg : p.1.degree < n := by
        have hd := congrArg Finsupp.degree hmem
        rw [map_add] at hd
        have : p.2.degree ≠ 0 := fun h0 => h2 ((Finsupp.degree_eq_zero_iff _).1 h0)
        omega
      exact mm_mul_ge (ih _ hdeg p.1 rfl r) (hMint i r p.2)
    simp only [hsplit, Finset.sum_add_distrib, hMc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h
    have h' := mm_sub h (mm_sum Finset.univ _ fun r _ => hrest r)
    rwa [add_sub_cancel_right] at h'

theorem mm_A_ndvd (hF : ∀ i, IntS V (G.F i)) (hA : IntS V A) (hc : IntS V c)
    (hlin : ∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A))
    (hfe : ∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c)))
    (μ : Fin 1 × Fin dd →₀ ℕ) (hμ : ¬ ∀ s, V.l ∣ μ s) : V.MM (MvPowerSeries.coeff μ A) := by
  push Not at hμ
  obtain ⟨s, hs⟩ := hμ
  have hpos : 1 ≤ μ s := by
    rcases Nat.eq_zero_or_pos (μ s) with h0 | h0
    · exact absurd (h0 ▸ dvd_zero V.l) hs
    · exact h0
  have hle : Finsupp.single s 1 ≤ μ := by
    intro t
    rw [Finsupp.single_apply]
    split_ifs with ht
    · rw [← ht]; exact hpos
    · exact Nat.zero_le _
  have hs' : s = ((0 : Fin 1), s.2) := Prod.ext (Subsingleton.elim _ _) rfl
  have h := mms_dA G hF hc hlin hfe s.2 (μ - Finsupp.single s 1)
  rw [← hs', MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle] at h
  have e : ((((μ - Finsupp.single s 1 : Fin 1 × Fin dd →₀ ℕ)) s : ℕ) : C) + 1 = ((μ s : ℕ) : C) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    push_cast [Nat.cast_sub hpos]
    ring
  rw [e, mul_comm] at h
  exact mm_of_natCast_mul hs (hA μ) h

theorem intS_sub' {σ : Type} {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f - g) := by
  intro μ
  have h1 := hf μ
  have h2 := hg μ
  unfold VF.Ge at h1 h2 ⊢
  rw [map_sub]
  exact le_trans (le_min h1 h2) (V.v.map_sub _ _)

theorem mms_frobTw_sub {σ : Type} {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) :
    MMS V (frobTw V.l (f - g) - (frobTw V.l f - frobTw V.l g)) := by
  have h1 := mms_frobTw_add hf (intS_neg hg)
  have h2 := mms_frobTw_neg hg
  rw [← sub_eq_add_neg] at h1
  have e : frobTw V.l (f - g) - (frobTw V.l f - frobTw V.l g) =
      (frobTw V.l (f - g) - (frobTw V.l f + frobTw V.l (-g))) + (frobTw V.l (-g) + frobTw V.l g) := by ring
  rw [e]
  exact h1.add h2

theorem eval_commutes_frobenius_twist {a : Pt C 2 dd} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, IntS V (a i)) {f : PS C 1 dd} (hf : IntS V f) :
    MMS V (ev (n := 2) ![a] (frobTw V.l f) - frobTw V.l (ev (n := 2) ![a] f)) := by
  have hI : ∀ p : Fin 1 × Fin dd, IntS V ((![a] : Fin 1 → Pt C 2 dd) p.1 p.2) := by
    intro p
    obtain ⟨k, i⟩ := p
    fin_cases k
    exact ha i
  exact mms_subst_frobTw (a := fun p : Fin 1 × Fin dd => (![a] : Fin 1 → Pt C 2 dd) p.1 p.2)
    (fun p => (z0_1 a ha0) p.1 p.2) hI hf

theorem integral_eval_single {a : Pt C 2 dd} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntS V (a i))
    {f : PS C 1 dd} (hf : IntS V f) : IntS V (ev (n := 2) ![a] f) :=
  intS_ev (z0_1 a ha0) (fun k i => by fin_cases k; exact ha i) hf

theorem maximal_eval_single {a : Pt C 2 dd} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntS V (a i))
    {f : PS C 1 dd} (hf : MMS V f) : MMS V (ev (n := 2) ![a] f) :=
  MMS.ev_of (z0_1 a ha0) (fun k i => by fin_cases k; exact ha i) hf

theorem cobd_eq (X : PS C 1 dd) :
    cobd G.F X = ev (n := 2) ![G.F] X - ev (n := 2) ![pt C dd 0] X - ev (n := 2) ![pt C dd 1] X := by
  unfold cobd
  rw [hadd G]

end ZeroPointGroupLaw

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence ZeroPointGroupLaw in

theorem first_step_second_half : FirstStepSecondHalfCondition := by
  intro C _ _ V hac dd G hF A c hA hc hlin hfe
  have := hac
  have hl := V.l_prime.pos
  have hroot : ∀ ν : Fin 1 × Fin dd →₀ ℕ, ∃ y : C, y ^ V.l = MvPowerSeries.coeff (V.l • ν) A :=
    fun ν => IsAlgClosed.exists_pow_nat_eq _ hl
  choose b hb using hroot
  let B : PS C 1 dd := fun ν => b ν
  have hBc : ∀ ν, MvPowerSeries.coeff ν B = b ν := fun ν => rfl
  have hB : IntS V B := fun ν => by
    rw [hBc]
    exact ge_of_pow (by rw [hb]; exact hA _)
  refine ⟨B, hB, ?_⟩
  have hpt0 : ∀ i, IntS V (pt C (n := 2) dd 0 i) := fun i => intS_X _
  have hpt1 : ∀ i, IntS V (pt C (n := 2) dd 1 i) := fun i => intS_X _

  have hN : MMS V (A - frobTw V.l B) := by
    intro μ
    rw [map_sub, coeff_frobTw]
    split_ifs with hdiv
    · rw [hBc, hb, smul_divl hdiv, sub_self]
      exact mm_zero
    · rw [sub_zero]
      exact mm_A_ndvd G hF hA hc hlin hfe μ hdiv
  have hFB : IntS V (frobTw V.l B) := intS_frobTw hB

  have hdN : MMS V (cobd G.F A - cobd G.F (frobTw V.l B)) := by
    rw [cobd_eq G, cobd_eq G]
    have e : ev (n := 2) ![G.F] A - ev (n := 2) ![pt C dd 0] A - ev (n := 2) ![pt C dd 1] A -
        (ev (n := 2) ![G.F] (frobTw V.l B) - ev (n := 2) ![pt C dd 0] (frobTw V.l B) -
          ev (n := 2) ![pt C dd 1] (frobTw V.l B)) =
        ev (n := 2) ![G.F] (A - frobTw V.l B) - ev (n := 2) ![pt C dd 0] (A - frobTw V.l B) -
          ev (n := 2) ![pt C dd 1] (A - frobTw V.l B) := by
      rw [ev_sub (z0_1 _ G.const), ev_sub (z0_1 _ (z0_pt 0)), ev_sub (z0_1 _ (z0_pt 1))]
      ring
    rw [e]
    exact ((maximal_eval_single G.const hF hN).sub (maximal_eval_single (z0_pt 0) hpt0 hN)).sub (maximal_eval_single (z0_pt 1) hpt1 hN)

  have hx1 := integral_eval_single G.const hF hB
  have hx2 := integral_eval_single (z0_pt 0) hpt0 hB
  have hx3 := integral_eval_single (z0_pt 1) hpt1 hB
  have hdF : MMS V (cobd G.F (frobTw V.l B) - frobTw V.l (cobd G.F B)) := by
    rw [cobd_eq G, cobd_eq G]
    have t1 := eval_commutes_frobenius_twist G.const hF hB
    have t2 := eval_commutes_frobenius_twist (z0_pt 0) hpt0 hB
    have t3 := eval_commutes_frobenius_twist (z0_pt 1) hpt1 hB
    have s1 := mms_frobTw_sub (intS_sub' hx1 hx2) hx3
    have s2 := mms_frobTw_sub hx1 hx2
    have e : ev (n := 2) ![G.F] (frobTw V.l B) - ev (n := 2) ![pt C dd 0] (frobTw V.l B) -
          ev (n := 2) ![pt C dd 1] (frobTw V.l B) -
        frobTw V.l (ev (n := 2) ![G.F] B - ev (n := 2) ![pt C dd 0] B - ev (n := 2) ![pt C dd 1] B) =
        (ev (n := 2) ![G.F] (frobTw V.l B) - frobTw V.l (ev (n := 2) ![G.F] B)) -
          (ev (n := 2) ![pt C dd 0] (frobTw V.l B) - frobTw V.l (ev (n := 2) ![pt C dd 0] B)) -
          (ev (n := 2) ![pt C dd 1] (frobTw V.l B) - frobTw V.l (ev (n := 2) ![pt C dd 1] B)) -
          (frobTw V.l (ev (n := 2) ![G.F] B - ev (n := 2) ![pt C dd 0] B) -
            (frobTw V.l (ev (n := 2) ![G.F] B) - frobTw V.l (ev (n := 2) ![pt C dd 0] B))) -
          (frobTw V.l (ev (n := 2) ![G.F] B - ev (n := 2) ![pt C dd 0] B - ev (n := 2) ![pt C dd 1] B) -
            (frobTw V.l (ev (n := 2) ![G.F] B - ev (n := 2) ![pt C dd 0] B) -
              frobTw V.l (ev (n := 2) ![pt C dd 1] B))) := by ring
    rw [e]
    exact (((t1.sub t2).sub t3).sub s2).sub s1
  have hcB : IntS V (cobd G.F B) := by
    rw [cobd_eq G]
    exact intS_sub' (intS_sub' hx1 hx2) hx3
  have hFc : MMS V (frobTw V.l c - frobTw V.l (cobd G.F B)) := by
    have e : frobTw V.l c - frobTw V.l (cobd G.F B) =
        -(cobd G.F A - frobTw V.l c) + (cobd G.F A - cobd G.F (frobTw V.l B)) +
          (cobd G.F (frobTw V.l B) - frobTw V.l (cobd G.F B)) := by ring
    rw [e]
    exact (((show MMS V (cobd G.F A - frobTw V.l c) from hfe).neg).add hdN).add hdF
  have hFd : MMS V (frobTw V.l (c - cobd G.F B)) := by
    have e : frobTw V.l (c - cobd G.F B) =
        (frobTw V.l (c - cobd G.F B) - (frobTw V.l c - frobTw V.l (cobd G.F B))) +
          (frobTw V.l c - frobTw V.l (cobd G.F B)) := by ring
    rw [e]
    exact (mms_frobTw_sub hc hcB).add hFc
  exact mms_of_frobTw hFd

theorem rank_maximal_of_first_half (hP : FirstStepFirstHalfCondition) : RankMaximalOfNondegenerate :=
  rank_maximal_of_halves hP first_step_second_half

end Formalism.L2.FormalSeriesBounds
