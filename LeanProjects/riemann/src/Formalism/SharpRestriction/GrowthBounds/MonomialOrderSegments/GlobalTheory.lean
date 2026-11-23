import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.TestBoundOfRhoAndNormSets

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def outB : D.ML → Bool :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (Sum.elim (fun _ => false) (fun _ => true)))

abbrev outP (i : D.ML) : Prop := D.outB i = true

def SameBlockAlt (ζ ζ' : D.EM) : Prop :=
  (∀ i, ldeg ζ' i = ldeg ζ i) ∧ (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧
    (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))

theorem SameBlockAlt.refl (ζ : D.EM) : D.SameBlockAlt ζ ζ := by
  unfold SameBlockAlt
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem GoodE.good_exponent_same_block {p : ℕ} {ζ ζ' : D.EM} (h : D.GoodE p ζ) (hb : D.SameBlockAlt ζ ζ') : D.GoodE p ζ' := by
  unfold GoodE at h ⊢
  unfold SameBlockAlt at hb
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hl, hlab, htp⟩ := hb
  refine ⟨fun t a => ?_, fun j m hm a => ?_, fun b => (hl _).trans (h3 b), fun t => ?_,
    fun t => (hl _).le.trans (h5 t)⟩
  · rw [hlab]; exact h1 t a
  · rw [htp]; exact h2 j m hm a
  · simp only [hl]; exact h4 t

theorem output_exponent_same_block {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') : eOut D.outP ζ' = eOut D.outP ζ := by
  unfold SameBlockAlt at hb
  obtain ⟨_, hlab, htp⟩ := hb
  ext ⟨i, a⟩
  simp only [eOut, Finsupp.filter_apply]
  split_ifs with h
  · rcases i with b | t | t | t
    · exact absurd h (by simp [outB])
    · exact hlab t a
    · exact absurd h (by simp [outB])
    · exact htp t a
  · rfl

theorem ldeg_eIn (ζ : D.EM) (i : D.ML) : ldeg (eIn D.outP ζ) i = if D.outP i then 0 else ldeg ζ i := by
  unfold ldeg eIn
  split_ifs with h
  · simp [Finsupp.filter_apply, h]
  · have h' : D.outB i = false := by simpa [outP] using h
    simp [Finsupp.filter_apply, h']

theorem tangent_exponent_same_block {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') : D.tpE ζ' = D.tpE ζ := by
  unfold SameBlockAlt at hb
  obtain ⟨_, _, htp⟩ := hb
  unfold tpE
  congr 1
  funext x
  rcases x with ⟨o | t, a⟩
  · rfl
  · exact htp t a

theorem label_function_same_block {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') : D.labF ζ' = D.labF ζ := by
  unfold SameBlockAlt at hb
  obtain ⟨_, hlab, _⟩ := hb
  funext t a
  exact hlab t a

def dUp : D.ML → ℕ :=
  Sum.elim D.dB (Sum.elim (fun _ => 0) (Sum.elim D.dT (fun _ => 0)))

theorem kapL_dUp (p : ℕ) : kapL p D.r D.dUp = kapL p D.r D.dO := by
  unfold kapL dUp dO
  first
    | (simp [Fintype.sum_sum_type]; done)
    | (simp [Fintype.sum_sum_type]; rfl)
    | (simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]; simp; rfl)

theorem ldeg_eIn_le {p : ℕ} (hp : 0 < p) {ζ : D.EM} (h : D.GoodE p ζ) (i : D.ML) :
    ldeg (eIn D.outP ζ) i ≤ D.dUp i := by
  rw [ldeg_eIn]
  unfold GoodE at h
  obtain ⟨_, _, h3, h4, _⟩ := h
  split_ifs with ho
  · exact Nat.zero_le _
  · rcases i with b | t | t | t
    · exact (h3 b).le
    · exact (ho rfl).elim
    · have hP : 1 ≤ D.P p t := Nat.one_le_pow _ _ hp
      show ldeg ζ (D.mw t) ≤ D.dT t
      have h4t := h4 t
      nlinarith [Nat.zero_le (ldeg ζ (D.mw t))]
    · exact (ho rfl).elim

variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem blk_fact (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ ζ' : D.EM} (h : D.GoodE p ζ) (hb : D.SameBlockAlt ζ ζ') :
    vN v (fact ζ') - vN v (fact ζ) ≤ D.kapD p := by
  have hp := two_le_p hD
  rw [fact_eq_out_mul_in D.outP ζ, fact_eq_out_mul_in D.outP ζ', D.output_exponent_same_block hb,
    vN_mul hD (fact_ne_zero _) (fact_ne_zero _), vN_mul hD (fact_ne_zero _) (fact_ne_zero _)]
  have e1 : ∀ i, ldeg (eIn D.outP ζ') i = ldeg (eIn D.outP ζ) i := by
    intro i; rw [ldeg_eIn, ldeg_eIn, hb.1 i]
  have h1 := fact_upper hD e1
  have h2 := fact_lower hD (α := eIn D.outP ζ) (d := fun i => ldeg (eIn D.outP ζ) i) (fun _ => rfl)
  have h3 : kapL p D.r (fun i => ldeg (eIn D.outP ζ) i) ≤ kapL p D.r D.dUp :=
    kapL_mono hp D.r (D.ldeg_eIn_le (by omega) h)
  have h4 := kapL_le_kap' hp hr D.dO
  rw [D.kapL_dUp] at h3
  have h5 : D.kapD p = kap p D.r D.dO := rfl
  rw [h5]; linarith

theorem wt_lower (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ : D.EM} (h : D.GoodE p ζ) :
    2 * D.n0 v - 2 * D.kapD p ≤ vN v (fact (D.collapseExponent p ζ)) + vN v (fact (D.tpE ζ)) := by
  have hp := two_le_p hD
  have h1 := fact_add_lower hD (α := D.collapseExponent p ζ) (α' := D.tpE ζ) (d := D.dO) (D.ldeg_phE p ζ h)
  have h4 := kapL_le_kap' hp hr D.dO
  have h5 : D.kapD p = kap p D.r D.dO := rfl
  have h6 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
  rw [h5, h6]; linarith

theorem fact_phE_lower (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ : D.EM} (h : D.GoodE p ζ) :
    2 * D.n0 v - D.kapD p ≤ vN v (fact (D.phE p ζ)) := by
  have hp := two_le_p hD
  have h1 := fact_lower hD (α := D.phE p ζ) (d := D.dO) (D.ldeg_phE p ζ h)
  have h4 := kapL_le_kap' hp hr D.dO
  have h5 : D.kapD p = kap p D.r D.dO := rfl
  have h6 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
  rw [h5, h6]; linarith

omit [CharZero K] in
theorem fact_EM (ζ : D.EM) : fact ζ = (∏ b, ∏ a, (ζ (D.mb b, a)).factorial) *
    ((∏ t, ∏ a, (ζ (D.mlab t, a)).factorial) * ((∏ t, ∏ a, (ζ (D.mw t, a)).factorial) *
      ∏ t, ∏ a, (ζ (D.mtp t, a)).factorial)) := by
  unfold fact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type]
  rfl

omit [CharZero K] in
theorem factorial_embedded_exponent (ζ : D.EM) : fact (D.collapseExponent p ζ) = (∏ b, ∏ a, (ζ (D.mb b, a)).factorial) *
    ∏ t, ∏ a, (ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a)).factorial := by
  unfold fact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type]
  simp [collapseExponent]

omit [CharZero K] in
theorem fact_tpE (ζ : D.EM) : fact (D.tpE ζ) = ∏ t, ∏ a, (ζ (D.mtp t, a)).factorial := by
  unfold fact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type]
  simp [tpE]

def kapC (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) (ζ : D.EM) : K :=
  (∏ t, cst t (D.labF ζ t) (ldeg ζ (D.mw t))) /
    ((∏ t : D.Tau, ∏ a, (ζ (D.mlab t, a)).factorial : ℕ) : K)

omit [CharZero K] in
theorem kappa_constant_same_block (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') :
    D.kapC cst ζ' = D.kapC cst ζ := by
  have hL := D.label_function_same_block hb
  unfold SameBlockAlt at hb
  obtain ⟨hl, hlab, _⟩ := hb
  unfold kapC
  rw [hL]
  simp only [hl, hlab]

theorem fact_eq_kapC {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) :
    (fact (D.collapseExponent p ζ) : K) * (fact (D.tpE ζ) : K) =
      D.kapC cst ζ * (∏ t, gam t (D.labF ζ t) (D.wF ζ t)) * (fact ζ : K) := by
  have h1 : ∀ t, ((∏ a, (ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a)).factorial : ℕ) : K) =
      cst t (D.labF ζ t) (ldeg ζ (D.mw t)) * ((∏ a, (ζ (D.mw t, a)).factorial : ℕ) : K) *
        gam t (D.labF ζ t) (D.wF ζ t) := fun t => ((hdig.1 t (D.labF ζ t) (hζ t)).2 (D.wF ζ t)).2
  have h0 : ((∏ t : D.Tau, ∏ a, (ζ (D.mlab t, a)).factorial : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun t _ => Finset.prod_ne_zero_iff.mpr fun a _ =>
      Nat.factorial_ne_zero _
  rw [factorial_embedded_exponent, fact_tpE, fact_EM, kapC]
  rw [Nat.cast_mul, Nat.cast_prod (s := (univ : Finset D.Tau))
    (f := fun t => ∏ a, (ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a)).factorial)]
  simp only [h1, Finset.prod_mul_distrib]
  push_cast
  push_cast at h0
  field_simp

theorem vge_kapC (hD : DVRHyp v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) :
    vge v (vN v (fact (D.collapseExponent p ζ)) + vN v (fact (D.tpE ζ)) - vN v (fact ζ)) (D.kapC cst ζ) := by
  have hd := hdig
  unfold DigOK at hd
  obtain ⟨h1, _⟩ := hd
  have heq := D.fact_eq_kapC hdig hζ
  have hG : v (∏ t, gam t (D.labF ζ t) (D.wF ζ t)) = 0 :=
    Finset.prod_induction _ (fun x => v x = 0)
      (fun a b ha hb => by rw [AddValuation.map_mul, ha, hb, add_zero]) (AddValuation.map_one v)
      (fun t _ => ((h1 t (D.labF ζ t) (fun a => hζ t a)).2 (D.wF ζ t)).1)
  have hfact : ∀ {σ : Type} (α : σ →₀ ℕ), ((fact α : ℕ) : K) ≠ 0 := fun α =>
    Nat.cast_ne_zero.2 (by
      unfold fact Finsupp.prod
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _)
  have hA := hfact (D.collapseExponent p ζ)
  have hB := hfact (D.tpE ζ)
  have hZ := hfact ζ
  have hX : D.kapC cst ζ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at heq
    exact mul_ne_zero hA hB heq
  obtain ⟨qA, hqA⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hA)
  obtain ⟨qB, hqB⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hB)
  obtain ⟨qZ, hqZ⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hZ)
  obtain ⟨qX, hqX⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.top_iff v).not.2 hX)
  have hv := congrArg v heq
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hG, ← hqA, ← hqB, ← hqZ,
    ← hqX] at hv
  have hq : qA + qB = qX + qZ := by
    have h2 : ((qA + qB : ℚ) : WithTop ℚ) = ((qX + qZ : ℚ) : WithTop ℚ) := by
      rw [WithTop.coe_add, WithTop.coe_add, hv, add_zero]
    exact WithTop.coe_eq_coe.1 h2
  unfold vge vR vN
  rw [← hqA, ← hqB, ← hqZ, ← hqX]
  simp only [WithTop.untopD_coe, WithTop.map_coe]
  have hle : (qA : ℝ) + qB - qZ ≤ qX := by
    have h3 : (qA : ℝ) + qB = qX + qZ := by exact_mod_cast hq
    linarith
  exact WithTop.coe_le_coe.2 hle

theorem digOK_exists (hDIG : DIG K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c) :
    ∃ cst gam, D.DigOK v p cst gam := by
  obtain ⟨cst, gam, h1, h2⟩ := hDIG hD D.Tau D.r D.g
  refine ⟨cst, gam, ?_⟩
  unfold DigOK
  exact ⟨h1, fun ρ hρ ε hε => h2 ρ hρ D.c hc ε hε⟩

end TwistData

end Formalism.MainNotions.PlaneGram
