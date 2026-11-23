import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.FrobPeriod

end GlobalTheory.QLog.FrobPeriod

namespace GlobalTheory.QLog

open MvPowerSeries in
set_option autoImplicit false in
private lemma coeff_single_inr_of_isLift {B O : Type} [CommRing B] [CommRing O] {θ : B →+* O} {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : _root_.GlobalTheory.QLog.IsLift θ μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr i) 1) (μ j) = if i = j then 1 else 0 := by
  have h0 := (_root_.GlobalTheory.coeff_subst_restrict_sum (μ j)).2 (Finsupp.single i 1)
  rw [Finsupp.mapDomain_single] at h0
  rw [← h0, ← hμ.comm j]
  unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.at2
  have ha : HasSubst (Sum.elim (fun k : Fin d => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) B))
      fun k : Fin d => X (Sum.inl k)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have hb : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B))
      fun k : Fin d => X k) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  rw [subst_comp_subst_apply ha hb]
  have hc : (fun s => subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B))
      fun k : Fin d => X k)
      (Sum.elim (fun k : Fin d => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) B))
        (fun k : Fin d => X (Sum.inl k)) s)) =
      Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) B)) fun _ : Fin d => 0 := by
    funext s
    cases s <;> simp [subst_X hb]
  rw [hc]
  have hadd := congrFun hμ.unit j
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.at2 at hadd
  rw [hadd, coeff_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Finsupp.single_left_inj]

open MvPowerSeries in
set_option autoImplicit false in
private lemma subst_inr_zero_map_eq_X_of_isLift {B O Q : Type} [CommRing B] [CommRing O] [CommRing Q] [Algebra B Q] {θ : B →+* O} {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : _root_.GlobalTheory.QLog.IsLift θ μ) (j : Fin d) :
    subst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q)) fun _ : Fin d => 0)
      (map (algebraMap B Q) (μ j)) = X j := by
  have hadd := congrFun hμ.unit j
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.at2 at hadd
  ext α
  rw [(_root_.GlobalTheory.coeff_subst_restrict_sum _).1 α, coeff_map,
    ← (_root_.GlobalTheory.coeff_subst_restrict_sum (μ j)).1 α, hadd, coeff_X, coeff_X]
  split_ifs <;> simp

open MvPowerSeries in
set_option autoImplicit false in
private lemma subst_zero_fin_eq_C_constantCoeff {Q : Type} [CommRing Q] {d : ℕ} (g : MvPowerSeries (Fin d) Q) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) Q)) g = C (constantCoeff g) := by
  have hz : HasSubst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  ext e
  rw [coeff_subst hz, finsum_eq_single _ 0]
  · simp only [coeff_C]
    simp [coeff_one]
  · intro n hn
    obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    rw [Finsupp.prod, Finset.prod_eq_zero (i := s) (by simpa using hs) (by simp [hs])]
    simp

open MvPowerSeries in
set_option autoImplicit false in
private lemma subst_inr_zero_pderiv_coboundary_eq {Q : Type} [CommRing Q] {d : ℕ} (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q)
    (hν0 : ∀ j, constantCoeff (ν j) = 0)
    (hν1 : ∀ j, subst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q)) fun _ : Fin d => 0)
      (ν j) = X j) (f : MvPowerSeries (Fin d) Q) (i : Fin d) :
    subst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q)) fun _ : Fin d => 0)
      (pderiv Q (Sum.inr i) (subst ν f - subst (fun k => X (Sum.inl k)) f -
        subst (fun k => X (Sum.inr k)) f)) =
      ∑ j, pderiv Q j f * subst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q))
        fun _ : Fin d => 0) (pderiv Q (Sum.inr i) (ν j)) - C (constantCoeff (pderiv Q i f)) := by
  have he0 : HasSubst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q))
      fun _ : Fin d => 0) := hasSubst_of_constantCoeff_zero (by rintro (k | k) <;> simp)
  have hν : HasSubst ν := hasSubst_of_constantCoeff_zero hν0
  have hL : HasSubst (fun k : Fin d => (X (Sum.inl k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hR : HasSubst (fun k : Fin d => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  rw [map_sub, map_sub, _root_.GlobalTheory.PSChain.pderiv_subst_chain _ hν0, _root_.GlobalTheory.PSChain.pderiv_subst_chain _ (by simp),
    _root_.GlobalTheory.PSChain.pderiv_subst_chain _ (by simp)]
  simp only [pderiv_X, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero,
    Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← coe_substAlgHom he0]
  simp only [map_sub, map_sum, map_mul]
  rw [coe_substAlgHom he0, subst_comp_subst_apply hR he0]
  simp only [subst_comp_subst_apply hν he0, hν1, subst_X he0, Sum.elim_inr]
  rw [subst_zero_fin_eq_C_constantCoeff]
  simp only [show (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q)) = X from rfl, subst_self, id]

open MvPowerSeries in
set_option autoImplicit false in
private lemma dIn_univ_of_QL_of_isLift {B O Q : Type} [CommRing B] [CommRing O]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : _root_.GlobalTheory.QLog.IsLift θ μ)
    {f : MvPowerSeries (Fin d) Q} (hf : _root_.GlobalTheory.QLog.QL μ ⊤ f) :
    _root_.GlobalTheory.QLog.DIn (⊤ : Ideal B) f := by
  obtain ⟨-, hlin, hcob⟩ := hf
  unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.QLog.up _root_.GlobalTheory.Katz.inL
    _root_.GlobalTheory.Katz.inR at hcob
  unfold _root_.GlobalTheory.Katz.lin at hlin
  set M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) := fun j i =>
    subst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) B)) fun _ : Fin d => 0)
      (pderiv B (Sum.inr i) (μ j)) with hMdef
  have hM : ∀ j i, constantCoeff (M j i) = if j = i then 1 else 0 := by
    intro j i
    rw [← coeff_zero_eq_constantCoeff_apply, hMdef, (_root_.GlobalTheory.coeff_subst_restrict_sum _).1 0,
      Finsupp.mapDomain_zero, coeff_pderiv, zero_add, coeff_single_inr_of_isLift hμ i j]
    simp [eq_comm]
  have hmap : ∀ j i, map (algebraMap B Q) (M j i) =
      subst (Sum.elim (fun k : Fin d => (X k : MvPowerSeries (Fin d) Q)) fun _ : Fin d => 0)
        (pderiv Q (Sum.inr i) (map (algebraMap B Q) (μ j))) := by
    intro j i
    ext α
    rw [coeff_map, hMdef, (_root_.GlobalTheory.coeff_subst_restrict_sum _).1 α,
      (_root_.GlobalTheory.coeff_subst_restrict_sum _).1 α, coeff_pderiv, coeff_pderiv, coeff_map]
    simp
  have hν1 := fun j => subst_inr_zero_map_eq_X_of_isLift (Q := Q) hμ j
  have hsol := _root_.GlobalTheory.InvSolve.solve (Q := Q) ⊤ M hM
    (fun j => pderiv Q j f) (fun i => ∑ j, pderiv Q j f * map (algebraMap B Q) (M j i))
    (fun i => rfl) ?_
  · intro α i
    by_cases hα : α i = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [hα]⟩
    · obtain ⟨b, -, hb⟩ := hsol i (α - Finsupp.single i 1)
      refine ⟨b, Submodule.mem_top, ?_⟩
      rw [← hb, coeff_pderiv, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr hα))]
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      rw [mul_comm]
      congr 1
      push_cast [Nat.one_le_iff_ne_zero.mpr hα]
      ring
  · intro i α
    simp only [hmap]
    have key := subst_inr_zero_pderiv_coboundary_eq (fun j => map (algebraMap B Q) (μ j))
      (fun j => by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
        coeff_zero_eq_constantCoeff_apply, hμ.const j, map_zero])
      hν1 f i
    rw [eq_sub_iff_add_eq] at key
    rw [← key, map_add, (_root_.GlobalTheory.coeff_subst_restrict_sum _).1 α, coeff_pderiv, coeff_C]
    obtain ⟨b, -, hb⟩ := hcob (Finsupp.mapDomain Sum.inl α + Finsupp.single (Sum.inr i) 1)
    obtain ⟨c, -, hc⟩ := hlin i
    refine ⟨b * ((Finsupp.mapDomain Sum.inl α (Sum.inr i) : ℕ) + 1) +
      (if α = 0 then c else 0), Submodule.mem_top, ?_⟩
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, hb]
    split_ifs <;> simp [hc]

open MvPowerSeries in
set_option autoImplicit false in
private lemma dIn_univ_map_of_compatible {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {σ : Type} (φ : B →+* B) (s : Q →+* Q) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b))
    {f : MvPowerSeries σ Q} (h : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal B) f) :
    _root_.GlobalTheory.QLog.DIn (⊤ : Ideal B) (map s f) := by
  unfold _root_.GlobalTheory.QLog.DIn at h ⊢
  intro α i
  obtain ⟨b, -, hb⟩ := h α i
  refine ⟨φ b, Submodule.mem_top, ?_⟩
  rw [coeff_map, ← hs, ← hb, map_mul, map_natCast]

open MvPowerSeries in
set_option autoImplicit false in
private lemma exists_pow_dvd_of_theta_pow_eq_mul {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hF : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    (z : B) (N : ℕ) (a : O) (h : θ z ^ N = (p : O) * a) : ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨b, rfl⟩ := hF.surj a
  have hk : θ (z ^ N - (p : B) * b) = 0 := by
    rw [map_sub, map_pow, map_mul, map_natCast, h, sub_self]
  obtain ⟨w, -, hw⟩ := hF.pd _ hk
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - (p : B) * b) ^ p := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ p)
    rw [sub_sub_cancel]
    exact dvd_mul_right _ _
  have h2 : z ^ (N * p) = ((z ^ N) ^ p - (z ^ N - (p : B) * b) ^ p) + (p : B) * w := by
    rw [← hw, pow_mul]; ring
  rw [h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
set_option autoImplicit false in
private lemma hasVal_map_of_compatible {p : ℕ} {B Q : Type} [CommRing B]
    [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ] [DecidableEq σ] (φ : B →+* B)
    (s : Q →+* Q) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b)) {z : σ → B}
    {f : MvPowerSeries σ Q} {q : Q} (h : _root_.GlobalTheory.QLog.HasVal p z f q) :
    _root_.GlobalTheory.QLog.HasVal p (fun i => φ (z i)) (map s f) (s q) := by
  unfold _root_.GlobalTheory.QLog.HasVal at h ⊢
  intro m
  obtain ⟨N, hN⟩ := h m
  refine ⟨N, fun N' hN' => ?_⟩
  obtain ⟨b, hb⟩ := hN N' hN'
  refine ⟨φ b, ?_⟩
  have key : MvPolynomial.eval (fun i => algebraMap B Q (φ (z i)))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') (map s f)) =
      s (MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') f)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext i
    simp [hs]
  rw [key, ← map_sub, hb, hs, map_mul, map_pow, map_natCast]

open MvPowerSeries in
set_option autoImplicit false in

theorem _root_.GlobalTheory.QLog.hasPeriod_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε,
    ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d)
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B),
    _root_.GlobalTheory.QLog.IsLift F.θ μ' →
    (∀ i, map F.θ (μ' i) = c.μ i) →
    ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B),
    _root_.GlobalTheory.QLog.QL μ' ⊤ f → c.HasPeriod F.θ t f y →
    c.HasPeriod F.θ t
      (_root_.GlobalTheory.QLog.frob p F.s f) (F.σ y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε F G d c μ' hlift hμ f t y hQL hper
  have hF := F.frame
  haveI := hF.complete
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hs := F.s_alg
  have hdiff : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B) f := dIn_univ_of_QL_of_isLift hlift hQL
  have hdiffs := dIn_univ_map_of_compatible _ _ hs hdiff
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hF] at hper ⊢
  intro n z hz
  obtain ⟨q, hq, b, hb⟩ := hper n z hz
  have hznil : ∀ i, ∃ N, (p : F.B) ∣ z i ^ N := by
    intro i
    obtain ⟨N, a, ha⟩ := c.nil n i
    refine exists_pow_dvd_of_theta_pow_eq_mul hF (z i) N ((t.pt n) a) ?_
    rw [hz i, ← map_pow, ha, map_mul, map_natCast]
  have hzpnil : ∀ i, ∃ N, (p : F.B) ∣ (z i ^ p) ^ N := by
    intro i
    obtain ⟨N, hN⟩ := hznil i
    exact ⟨N, by rw [← pow_mul, mul_comm, pow_mul]; exact dvd_pow hN hp0⟩
  have hσnil : ∀ i, ∃ N, (p : F.B) ∣ F.σ (z i) ^ N := by
    intro i
    obtain ⟨N, a, ha⟩ := hznil i
    exact ⟨N, ⟨F.σ a, by rw [← map_pow, ha, map_mul, map_natCast]⟩⟩
  have h1 := hasVal_map_of_compatible (p := p) _ _ hs hq
  obtain ⟨q', hq', -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ _ _ F.θ
    hF (Fin d) (fun i => z i ^ p) hzpnil _ hdiffs
  have hPD : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ w ∈ Ideal.span {(p : F.B)},
      x ^ p = (p : F.B) * w := by
    intro x hx
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨(p : F.B) ^ (p - 1) * e ^ p, ?_, ?_⟩
    · refine Ideal.mem_span_singleton.mpr (Dvd.dvd.mul_right (dvd_pow_self _ ?_) _)
      have := (Fact.out : p.Prime).two_le
      omega
    · rw [mul_pow, ← mul_assoc, ← pow_succ']
      congr 2
      have := (Fact.out : p.Prime).one_le
      omega
  have hcong : ∀ i, F.σ (z i) - z i ^ p ∈ Ideal.span {(p : F.B)} :=
    fun i => Ideal.mem_span_singleton.mpr (F.σ_pow (z i))
  obtain ⟨e, -, e', hee⟩ := _root_.GlobalTheory.HasValCong.hasVal_sub_mem p _ _ _ F.θ hF
    (Fin d) (fun i => F.σ (z i)) hσnil _ hPD (fun i => z i ^ p) _ _ _ hcong hdiffs
    h1 hq' 0
  obtain ⟨⟨E, hE, -⟩, -⟩ := _root_.GlobalTheory.CEval.continuous_eval p F.B
    F.B (Fin d) z hznil
  have hEX : (fun j => E ((X j : MvPowerSeries (Fin d) F.B) ^ p)) =
      fun j => z j ^ p := by
    funext j
    rw [map_pow, hE.1 j]
  have hfrob := _root_.GlobalTheory.QLog.hasVal_subst p _ _ _ F.θ hF (Fin d) z
    hznil E hE (Fin d) (fun j => (X j : MvPowerSeries (Fin d) F.B) ^ p) _ q'
    (fun j => by simp [hp0]) hdiffs (by rw [hEX]; exact hq')
  have hu : _root_.GlobalTheory.QLog.up F.Q
      (fun j => (X j : MvPowerSeries (Fin d) F.B) ^ p) = fun j => X j ^ p := by
    funext j
    simp [_root_.GlobalTheory.QLog.up]
  rw [hu] at hfrob
  refine ⟨q', by unfold _root_.GlobalTheory.QLog.frob; exact hfrob,
    F.σ b - (e + e'), ?_⟩
  have hs' := congrArg F.s hb
  simp only [map_mul, map_pow, map_natCast, hs, map_add] at hs'
  simp only [pow_zero, one_mul, map_add] at hee
  simp only [map_add, map_mul, map_sub, map_pow, map_natCast]
  linear_combination hs' - (p : F.Q) ^ n * hee

end GlobalTheory.QLog
