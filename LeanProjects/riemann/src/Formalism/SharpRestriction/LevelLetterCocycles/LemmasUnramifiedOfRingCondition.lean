import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.ToolsR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

theorem weierP {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A]
    (hpu : ¬ IsUnit p) (N : ℕ) (g h : PowerSeries A) (hg : IsUnit (constantCoeff g)) :
    ∃ (P : Polynomial A) (u : PowerSeries A), IsUnit u ∧ P.Monic ∧ P.natDegree = N ∧
      (∀ k < N, p ∣ P.coeff k) ∧ g * X ^ N + C p * h = (P : PowerSeries A) * u := by
  set I : Ideal A := Ideal.span {p} with hIdef
  set F : PowerSeries A := g * X ^ N + C p * h with hF
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hpu
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hAnt : Nontrivial A := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hpu (isUnit_of_subsingleton p)
  have hpI : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
  have hJ : ∀ x ∈ I, ∀ y : A, IsUnit (x * y + 1) := fun x hx y =>
    Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I hx) y
  have hmap : F.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I) * X ^ N := by
    simp [hF, map_C, hpI]
  have hg0 : Ideal.Quotient.mk I (constantCoeff g) ≠ 0 := (hg.map _).ne_zero
  have hord : (F.map (Ideal.Quotient.mk I)).order.toNat = N := by
    rw [hmap]
    have hoN : (g.map (Ideal.Quotient.mk I) * X ^ N).order = (N : ℕ∞) := by
      rw [order_eq_nat]
      refine ⟨?_, fun i hi => ?_⟩
      · rw [coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_map, coeff_zero_eq_constantCoeff]
        exact hg0
      · rw [coeff_mul_X_pow', if_neg (by omega)]
    rw [hoN]
    rfl
  have hdiv : F.IsWeierstrassDivisorAt I := by
    unfold IsWeierstrassDivisorAt
    rw [hord]
    have hc : coeff N F = constantCoeff g * (p * (coeff N h * ↑hg.unit⁻¹) + 1) := by
      have e : constantCoeff g * ↑hg.unit⁻¹ = 1 := hg.mul_val_inv
      rw [hF, map_add, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_C_mul,
        coeff_zero_eq_constantCoeff]
      linear_combination (-(p * coeff N h)) * e
    rw [hc]
    exact hg.mul (hJ p (Ideal.mem_span_singleton_self p) _)
  have HD := hdiv.isWeierstrassDivisionAt_div_mod (f := (X : PowerSeries A) ^ N)
  set q := hdiv.div ((X : PowerSeries A) ^ N)
  set r := hdiv.mod ((X : PowerSeries A) ^ N)
  have hdeg : r.degree < (N : WithBot ℕ) := by
    have := HD.degree_lt
    rw [hord] at this
    exact this
  have heq : (X : PowerSeries A) ^ N = F * q + (r : PowerSeries A) := HD.eq_mul_add

  have hq : IsUnit q := by
    have h1 := congrArg (fun x => coeff N (x.map (Ideal.Quotient.mk I))) heq
    simp only [map_add, map_mul, map_pow, map_X, coeff_X_pow_self] at h1
    rw [hmap, ← Polynomial.polynomial_map_coe, Polynomial.coeff_coe,
      Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_degree_lt hdeg, map_zero, add_zero,
      mul_assoc, mul_comm (X ^ N), ← mul_assoc, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      ← map_mul, coeff_map, coeff_zero_eq_constantCoeff] at h1
    have h1' : Ideal.Quotient.mk I (constantCoeff g * constantCoeff q) = 1 := by
      rw [← map_mul constantCoeff]
      exact h1.symm
    have h2 : constantCoeff g * constantCoeff q - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1', map_one, sub_self]
    have h3 := hJ _ h2 1
    rw [mul_one, sub_add_cancel] at h3
    rw [isUnit_iff_constantCoeff]
    exact isUnit_of_mul_isUnit_right h3
  refine ⟨Polynomial.X ^ N - r, ↑hq.unit⁻¹, Units.isUnit _, ?_, ?_, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow N).sub_of_left (by rwa [Polynomial.degree_X_pow])
  · have hdN : (Polynomial.X ^ N - r).degree = (N : WithBot ℕ) := by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
        Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdN
  · intro k hk
    have := HD.coeff_f_sub_r_mem (i := k) (by rw [hord]; exact hk)
    rw [map_sub, coeff_X_pow, if_neg (by omega), zero_sub, Polynomial.coeff_coe] at this
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega), zero_sub]
    exact Ideal.mem_span_singleton.mp this
  · rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, heq, add_sub_cancel_right,
      mul_assoc, IsUnit.mul_val_inv, mul_one]

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}

open Formalism.MainNotions.WachCoordinates

abbrev RingP (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))

theorem eat_qP :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qP W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP, LocWach.π₀]

theorem two_le : 2 ≤ PD.p := PD.hp.two_le

theorem pS_sub (s : ℕ) : pS W s - ((PD.p : ℕ) : LetA O n) = (W.φA ^ s) W.π₀ := by
  unfold pS qP
  rw [map_add, map_natCast]
  ring

theorem tools1 (hR : RingP W) :
    ∃ u : LetA O n, IsUnit u ∧ W.φA W.π₀ = u * W.π₀ * qP W ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
  exact ⟨w, w.isUnit, by rw [hw, eat_qP]⟩

theorem φpow_π₀ (hR : RingP W) : ∀ s : ℕ, ∃ a, (W.φA ^ s) W.π₀ = W.π₀ * a
  | 0 => ⟨1, by simp⟩
  | s + 1 => by
    obtain ⟨a, ha⟩ := φpow_π₀ hR s
    obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
    rw [eat_qP] at hw
    exact ⟨(w : LetA O n) * qP W ^ (PD.p - 1) * W.φA a, by
      rw [pow_succ', AlgHom.mul_apply, ha, map_mul, hw]; ring⟩

theorem φpow_qP (hR : RingP W) (s : ℕ) (hs : 1 ≤ s) : ∃ a, (W.φA ^ s) W.π₀ = qP W * a := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨a, ha⟩ := φpow_π₀ hR t
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
  rw [eat_qP] at hw
  have e : PD.p - 1 = (PD.p - 2) + 1 := by have := two_le (PD := PD); omega
  exact ⟨(w : LetA O n) * W.π₀ * qP W ^ (PD.p - 2) * W.φA a, by
    rw [pow_succ', AlgHom.mul_apply, ha, map_mul, hw, e, pow_succ]; ring⟩

theorem tools3 (hR : RingP W) (s : ℕ) :
    pS W s - ((PD.p : ℕ) : LetA O n) ∈ Ideal.span {W.π₀} := by
  rw [pS_sub]
  obtain ⟨a, ha⟩ := φpow_π₀ hR s
  rw [ha]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem tools4 (hR : RingP W) (s : ℕ) (hs : 1 ≤ s) :
    pS W s - ((PD.p : ℕ) : LetA O n) ∈ Ideal.span {qP W} := by
  rw [pS_sub]
  obtain ⟨a, ha⟩ := φpow_qP hR s hs
  rw [ha]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem π₀_comp (hR : RingP W) :
    ∃ w : PowerSeries O, IsUnit w ∧ W.π₀₁ = w * X ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  refine ⟨(w : LetA O n) 0, (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0)), ?_⟩
  have := congrFun hw 0
  simpa [LocWach.π₀, letπ] using this

theorem π₀₁_cc (hR : RingP W) : constantCoeff W.π₀₁ = 0 := by
  obtain ⟨w, _, hw⟩ := π₀_comp hR
  have h2 : 2 ≤ PD.p := two_le
  rw [hw, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero]

variable [IsDomain O]

theorem π₀₁_ne (hR : RingP W) : W.π₀₁ ≠ 0 := by
  obtain ⟨w, hwu, hw⟩ := π₀_comp hR
  rw [hw]
  exact mul_ne_zero hwu.ne_zero (pow_ne_zero _ X_ne_zero)

theorem q_component_ne_zero' (hR : RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) (i : ZMod n) : qP W i ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simp only [qP, Pi.add_apply, LocWach.π₀, Pi.natCast_apply, map_add, π₀₁_cc hR, map_natCast,
    zero_add, map_zero] at this
  exact hp0 this

theorem cancel_comp {a b c : LetA O n} (hc : ∀ i, c i ≠ 0) (h : c * a = c * b) : a = b := by
  funext i
  exact mul_left_cancel₀ (hc i) (congrFun h i)

theorem cancel_AΔ {a c : LetA O n} (hc : c ∈ W.AΔ) (hc0 : ∀ i, c i ≠ 0) (h : c * a ∈ W.AΔ) :
    a ∈ W.AΔ := by
  intro δ hδ
  apply cancel_comp hc0
  have e := h δ hδ
  rw [map_mul, hc δ hδ] at e
  exact e

theorem φ_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.φA a ∈ W.AΔ := by
  intro δ hδ
  rw [← W.φA_γA, ha δ hδ]

theorem φpow_AΔ (s : ℕ) {a : LetA O n} (ha : a ∈ W.AΔ) : (W.φA ^ s) a ∈ W.AΔ := by
  induction s with
  | zero => simpa using ha
  | succ s ih =>
    rw [pow_succ']
    change W.φA ((W.φA ^ s) a) ∈ W.AΔ
    exact φ_AΔ ih

theorem qP_AΔ (hR : RingP W) : qP W ∈ W.AΔ :=
  W.AΔ.add_mem hR.1 (Subalgebra.natCast_mem _ _)

theorem w_AΔ (hR : RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) {w : (LetA O n)ˣ}
    (hw : W.φA W.π₀ = (w : LetA O n) * W.π₀ * qP W ^ (PD.p - 1)) : (w : LetA O n) ∈ W.AΔ := by
  have hc : W.π₀ * qP W ^ (PD.p - 1) ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem (qP_AΔ hR) _)
  refine cancel_AΔ hc (fun i => ?_) ?_
  · simp only [Pi.mul_apply, Pi.pow_apply]
    exact mul_ne_zero (π₀₁_ne hR) (pow_ne_zero _ (q_component_ne_zero' hR hp0 i))
  · have : W.π₀ * qP W ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ := by rw [hw]; ring
    rw [this]
    exact φ_AΔ hR.1

theorem modp (hR : RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) : ∀ s : ℕ, ∃ v ∈ W.AΔ, IsUnit v ∧
    ∃ r : LetA O n, (W.φA ^ s) W.π₀ = v * W.π₀ ^ (PD.p ^ s) + ((PD.p : ℕ) : LetA O n) * r
  | 0 => ⟨1, W.AΔ.one_mem, isUnit_one, 0, by simp⟩
  | s + 1 => by
    obtain ⟨v, hvΔ, hvu, r, hr⟩ := modp hR hp0 s
    obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
    rw [eat_qP] at hw
    have hwΔ := w_AΔ hR hp0 hw
    set a := (W.φA ^ s) W.π₀ with ha
    have hq : (W.φA ^ s) (qP W) = a + ((PD.p : ℕ) : LetA O n) := by
      unfold qP; rw [map_add, map_natCast]
    have e : (W.φA ^ (s + 1)) W.π₀ = (W.φA ^ s) w * a * (a + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1) := by
      rw [pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul, map_pow, hq]
    have d1 : ((PD.p : ℕ) : LetA O n) ∣ a * (a + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1) - a ^ PD.p := by
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (a + ((PD.p : ℕ) : LetA O n)) a (PD.p - 1)
      have e1 : a ^ PD.p = a * a ^ (PD.p - 1) := by
        rw [← pow_succ']; congr 1; have := two_le (PD := PD); omega
      refine ⟨a * c, ?_⟩
      rw [e1, ← mul_sub, hc]
      ring
    have d2 : ((PD.p : ℕ) : LetA O n) ∣ a ^ PD.p - (v * W.π₀ ^ (PD.p ^ s)) ^ PD.p := by
      have := sub_dvd_pow_sub_pow a (v * W.π₀ ^ (PD.p ^ s)) PD.p
      have hra : a - v * W.π₀ ^ (PD.p ^ s) = ((PD.p : ℕ) : LetA O n) * r := by rw [hr]; ring
      rw [hra] at this
      exact dvd_trans (dvd_mul_right _ _) this
    obtain ⟨c, hc⟩ : ((PD.p : ℕ) : LetA O n) ∣ (W.φA ^ (s + 1)) W.π₀ -
        ((W.φA ^ s) w * v ^ PD.p) * W.π₀ ^ (PD.p ^ (s + 1)) := by
      rw [e]
      have : (W.φA ^ s) w * a * (a + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1) -
          ((W.φA ^ s) w * v ^ PD.p) * W.π₀ ^ (PD.p ^ (s + 1)) =
          (W.φA ^ s) w * ((a * (a + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1) - a ^ PD.p) +
            (a ^ PD.p - (v * W.π₀ ^ (PD.p ^ s)) ^ PD.p)) := by
        rw [pow_succ PD.p s, pow_mul]; ring
      rw [this]
      exact dvd_mul_of_dvd_right (dvd_add d1 d2) _
    refine ⟨(W.φA ^ s) w * v ^ PD.p, W.AΔ.mul_mem (φpow_AΔ s hwΔ) (W.AΔ.pow_mem hvΔ _),
      (w.isUnit.map (W.φA ^ s)).mul (hvu.pow _), c, ?_⟩
    linear_combination hc

theorem φ_const (c : PowerSeries O) : W.φA (fun _ => c) = fun _ => W.φ₀ c := by
  funext i
  simp [LocWach.φA, letφ]

theorem pS_const (s : ℕ) : ∃ c : PowerSeries O, pS W s = fun _ => c := by
  unfold pS
  induction s with
  | zero => exact ⟨W.π₀₁ + ((PD.p : ℕ) : PowerSeries O), by funext i; simp [qP, LocWach.π₀]⟩
  | succ s ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨W.φ₀ c, by rw [pow_succ', AlgHom.mul_apply, hc, φ_const]⟩

theorem cc_subst {a : PowerSeries O} (ha : constantCoeff a = 0) (f : PowerSeries O) :
    constantCoeff (subst a f) = constantCoeff f := by
  erw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    erw [map_pow, ha, zero_pow hd, smul_zero]

theorem tools2 (hR : RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (s : ℕ) :
    ∃ (u : LetA O n) (P : Polynomial O), IsUnit u ∧ P.Monic ∧ P.natDegree = PD.p ^ s ∧
      (∀ k < PD.p ^ s, ((PD.p : ℕ) : O) ∣ P.coeff k) ∧ pS W s = u * Polynomial.aeval W.π₀ P := by
  set pA : LetA O n := ((PD.p : ℕ) : LetA O n) with hpA
  obtain ⟨v, hvΔ, hvu, r, hr⟩ := modp hR hp0 s
  have hpS : pS W s = v * W.π₀ ^ (PD.p ^ s) + pA * (r + 1) := by
    have := pS_sub (W := W) s
    rw [hr] at this
    linear_combination this
  have hpSΔ : pS W s ∈ W.AΔ := φpow_AΔ s (qP_AΔ hR)
  have hpΔ : pA ∈ W.AΔ := Subalgebra.natCast_mem _ _
  have hr1 : r + 1 ∈ W.AΔ := by
    refine cancel_AΔ hpΔ (fun i => ?_) ?_
    · simp only [hpA, Pi.natCast_apply]
      exact_mod_cast (by
        intro h
        have := congrArg constantCoeff h
        simp only [map_natCast, map_zero] at this
        exact hp0 this : ((PD.p : ℕ) : PowerSeries O) ≠ 0)
    · have : pA * (r + 1) = pS W s - v * W.π₀ ^ (PD.p ^ s) := by rw [hpS]; ring
      rw [this]
      exact W.AΔ.sub_mem hpSΔ (W.AΔ.mul_mem hvΔ (W.AΔ.pow_mem hR.1 _))
  obtain ⟨g, hg, -⟩ := hR.2.1 v hvΔ
  obtain ⟨h, hh, -⟩ := hR.2.1 (r + 1) hr1
  have ha0 : constantCoeff (W.π₀ 0) = 0 := π₀₁_cc hR
  have hs0 := HasSubst.of_constantCoeff_zero' ha0
  have hgu : IsUnit (constantCoeff (g 0)) := by
    have hv0 : IsUnit (v 0) := hvu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0)
    rw [hg 0] at hv0
    have := hv0.map constantCoeff
    rwa [cc_subst ha0] at this
  obtain ⟨P, u0, hu0, hPm, hPd, hPc, hF⟩ :=
    weierP ((PD.p : ℕ) : O) hpu (PD.p ^ s) (g 0) (h 0) hgu
  refine ⟨fun _ => subst (W.π₀ 0) u0, P, ?_, hPm, hPd, hPc, ?_⟩
  · rw [Pi.isUnit_iff]
    intro i
    rw [← coe_substAlgHom hs0]
    exact hu0.map _
  · obtain ⟨c, hc⟩ := pS_const (W := W) s
    have h0 : pS W s 0 = subst (W.π₀ 0) ((P : PowerSeries O) * u0) := by
      rw [← hF, ← coe_substAlgHom hs0]
      have e : pS W s 0 = v 0 * W.π₀ 0 ^ (PD.p ^ s) + ((PD.p : ℕ) : PowerSeries O) * (r + 1) 0 := by
        rw [hpS]; rfl
      rw [e, hg 0, hh 0, ← coe_substAlgHom hs0]
      simp [map_add, map_mul, map_pow, substAlgHom_X, map_natCast]
    funext i
    have e1 : pS W s i = pS W s 0 := by rw [hc]
    have e2 : (Polynomial.aeval W.π₀ P) i = Polynomial.aeval (W.π₀ 0) P := by
      exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i) W.π₀ P).symm
    rw [Pi.mul_apply, e1, e2, h0, subst_mul hs0, subst_coe hs0, mul_comm]

end W

end Formalism.MainNotions.UnusedSlot80.ToolsR

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem tool_algebra_of_ring_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL h _
  have hR : ToolsR.RingP ((HW l).W K 1 LL h.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O ((HW l).W K 1 LL h.2.2)
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  exact ⟨ToolsR.tools1 hR, ToolsR.tools2 hR hp0 hpu, ToolsR.tools3 hR, ToolsR.tools4 hR⟩

def LevCoeff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL h.2.2)

theorem tools_unramified_of_ring_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hL : LevCoeff D HW F) :
    FiltrationPropertiesEtale D HW F Cm := fun l _ K LL h h5 =>
  ⟨tool_algebra_of_ring_condition D HW F h9 l K LL h h5, hL l K LL h h5⟩

theorem tools_unramified_of_level_coeff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hL : LevCoeff D HW F) : FiltrationPropertiesTheorem D HW F Cm := fun h =>
  tools_unramified_of_ring_condition D HW F Cm h.2.2 hL

end Formalism.MainNotions.UnusedSlot80
