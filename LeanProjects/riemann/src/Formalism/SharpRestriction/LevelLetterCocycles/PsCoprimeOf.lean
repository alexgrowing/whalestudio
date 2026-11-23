import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.KF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL Formalism.MainNotions.UnusedSlot80.ToolsR Formalism.MainNotions.WachCoordinates

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

private lemma gammaA_apply_eq_gamma0 (W : LocWach PD LL O v n) (g : W.Gam) (a : LetA O n) (i : ZMod n) :
    W.γA g a i = W.γ₀ g (a i) := rfl

private lemma phiA_apply_eq_phi0_pred (W : LocWach PD LL O v n) (a : LetA O n) (i : ZMod n) :
    W.φA a i = W.φ₀ (a (i - 1)) := rfl

private lemma gammaA_phiA_comm (W : LocWach PD LL O v n) (g : W.Gam) (a : LetA O n) :
    W.γA g (W.φA a) = W.φA (W.γA g a) := by
  funext i
  simp only [gammaA_apply_eq_gamma0, phiA_apply_eq_phi0_pred]
  exact (W.γ₀_comm g (a (i - 1))).symm

theorem γA_φpow (W : LocWach PD LL O v n) (g : W.Gam) (t : ℕ) (a : LetA O n) :
    W.γA g ((W.φA ^ t) a) = (W.φA ^ t) (W.γA g a) := by
  induction t generalizing a with
  | zero => simp only [pow_zero, AlgHom.one_apply]
  | succ t ih =>
    rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, ih, gammaA_phiA_comm]

private lemma mem_AΔ_iff_forall_gammaA_fixed (W : LocWach PD LL O v n) (a : LetA O n) :
    a ∈ W.AΔ ↔ ∀ δ ∈ W.DelF, W.γA δ a = a := Iff.rfl

private lemma gammaA_comm_level_letter_cocycles (W : LocWach PD LL O v n) (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  funext i
  simp only [gammaA_apply_eq_gamma0]
  have e1 : W.γ₀ (g * h) = W.γ₀ (h * g) := by rw [mul_comm]
  rw [map_mul, map_mul] at e1
  have e2 := congrArg (fun f : PowerSeries O →ₐ[O] PowerSeries O => f (a i)) e1
  simpa only [AlgHom.mul_apply] using e2

private lemma phiA_pow_mem_AΔ (W : LocWach PD LL O v n) (t : ℕ) {a : LetA O n} (ha : a ∈ W.AΔ) :
    (W.φA ^ t) a ∈ W.AΔ := by
  rw [mem_AΔ_iff_forall_gammaA_fixed] at ha ⊢
  intro δ hδ
  rw [γA_φpow, ha δ hδ]

private lemma gammaA_mem_AΔ_of_mem (W : LocWach PD LL O v n) (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) :
    W.γA g a ∈ W.AΔ := by
  rw [mem_AΔ_iff_forall_gammaA_fixed] at ha ⊢
  intro δ hδ
  rw [gammaA_comm_level_letter_cocycles, ha δ hδ]

private lemma natCast_p_ne_zero_level_letter_cocycles (W : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have e := W.v_l
  rw [← map_natCast (algebraMap O LL) PD.p, h, map_zero, AddValuation.map_zero] at e
  simp at e

private lemma constantCoeff_phi0_eq_zero_of_eq_zero (W : LocWach PD LL O v n) (f : PowerSeries O)
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (W.φ₀ f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [map_mul, W.φ₀_X, map_mul, map_mul, PowerSeries.constantCoeff_X, zero_mul, zero_mul]

private lemma constantCoeff_phiA_pow_eq_zero_of_eq_zero (W : LocWach PD LL O v n) (s : ℕ) (a : LetA O n)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : ZMod n) :
    PowerSeries.constantCoeff ((W.φA ^ s) a i) = 0 := by
  induction s generalizing i with
  | zero => simpa only [pow_zero, AlgHom.one_apply] using ha i
  | succ s ih =>
    rw [pow_succ', AlgHom.mul_apply, phiA_apply_eq_phi0_pred]
    exact constantCoeff_phi0_eq_zero_of_eq_zero W _ (ih _)

private lemma constantCoeff_pi0_eq_zero_of_RingP (W : LocWach PD LL O v n) (hR : RingP W) (i : ZMod n) :
    PowerSeries.constantCoeff (W.π₀ i) = 0 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hR
  have h2 := PD.hp.two_le
  rw [hw, Pi.mul_apply, Pi.pow_apply, map_mul, map_pow]
  simp only [letπ, PowerSeries.constantCoeff_X]
  rw [zero_pow (by omega), mul_zero]

private lemma constantCoeff_ps_eq_p (W : LocWach PD LL O v n) (hR : RingP W) (s : ℕ) (i : ZMod n) :
    PowerSeries.constantCoeff (ps W s i) = ((PD.p : ℕ) : O) := by
  have e : ps W s = (W.φA ^ s) W.π₀ + ((PD.p : ℕ) : LetA O n) := by
    simp only [ps, qA, lA, map_add, map_natCast]
  rw [e, Pi.add_apply, map_add, constantCoeff_phiA_pow_eq_zero_of_eq_zero W s _ (constantCoeff_pi0_eq_zero_of_RingP W hR) i, zero_add,
    Pi.natCast_apply, map_natCast]

private lemma ps_apply_ne_zero (W : LocWach PD LL O v n) (hR : RingP W) (s : ℕ) (i : ZMod n) :
    ps W s i ≠ 0 := by
  intro h
  have e := constantCoeff_ps_eq_p W hR s i
  rw [h, map_zero] at e
  exact natCast_p_ne_zero_level_letter_cocycles W e.symm

private lemma pi0_mem_AΔ (W : LocWach PD LL O v n) (hR : RingP W) : W.π₀ ∈ W.AΔ := by
  obtain ⟨h1, -⟩ := hR
  exact h1

private lemma ps_mem_AΔ' (W : LocWach PD LL O v n) (hR : RingP W) (s : ℕ) : ps W s ∈ W.AΔ := by
  have hq : qA W ∈ W.AΔ := by
    show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
    exact add_mem (pi0_mem_AΔ W hR) (natCast_mem _ _)
  exact phiA_pow_mem_AΔ W s hq

private lemma mem_AΔ_of_ps_mul_mem_AΔ [IsDomain O] (W : LocWach PD LL O v n) (hR : RingP W) (s : ℕ)
    {x : LetA O n} (hx : ps W s * x ∈ W.AΔ) : x ∈ W.AΔ := by
  have hz := ps_mem_AΔ' W hR s
  rw [mem_AΔ_iff_forall_gammaA_fixed] at hx hz ⊢
  intro δ hδ
  have e1 := hx δ hδ
  rw [map_mul, hz δ hδ] at e1
  funext i
  have e2 := congrFun e1 i
  simp only [Pi.mul_apply] at e2
  exact mul_left_cancel₀ (ps_apply_ne_zero W hR s i) e2

private lemma isUnit_one_add_mul_pi0 (W : LocWach PD LL O v n) (hR : RingP W) (w : LetA O n) :
    IsUnit (1 + w * W.π₀) := by
  rw [Pi.isUnit_iff]
  intro i
  rw [PowerSeries.isUnit_iff_constantCoeff, Pi.add_apply, Pi.one_apply, Pi.mul_apply, map_add,
    map_one, map_mul, constantCoeff_pi0_eq_zero_of_RingP W hR i, mul_zero, add_zero]
  exact isUnit_one

private lemma mem_AΔ_of_mul_eq_one (W : LocWach PD LL O v n) {r r' : LetA O n} (hr : r ∈ W.AΔ)
    (h : r * r' = 1) : r' ∈ W.AΔ := by
  rw [mem_AΔ_iff_forall_gammaA_fixed] at hr ⊢
  intro δ hδ
  have e := congrArg (W.γA δ) h
  rw [map_mul, map_one, hr δ hδ] at e
  calc W.γA δ r' = r' * (r * W.γA δ r') := by rw [← mul_assoc, mul_comm r' r, h, one_mul]
    _ = r' := by rw [e, mul_one]

private lemma Eat_X_add_p_pi0_eq_qA (W : LocWach PD LL O v n) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      qA W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]

theorem psStable_of [IsDomain O] [NeZero n] (W : LocWach PD LL O v n) (hR : RingP W) : PsStable W := by
  have hR' := hR
  obtain ⟨-, -, -, -, -, -, ⟨w, hw⟩, -⟩ := hR'
  have hw' : W.γA W.gam W.π₀ - W.π₀ = (w : LetA O n) * W.π₀ * qA W := by
    rw [hw, Eat_X_add_p_pi0_eq_qA]
  have hγq : W.γA W.gam (qA W) = qA W * (1 + (w : LetA O n) * W.π₀) := by
    have e : W.γA W.gam (qA W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [qA, lA, map_add, map_natCast]
    rw [e, sub_eq_iff_eq_add.mp hw']
    simp only [qA, lA]
    ring
  have hq : qA W ∈ W.AΔ := by
    have e : ps W 0 = qA W := by simp only [ps, pow_zero, AlgHom.one_apply]
    rw [← e]
    exact ps_mem_AΔ' W hR 0
  have hu : 1 + (w : LetA O n) * W.π₀ ∈ W.AΔ := by
    apply mem_AΔ_of_ps_mul_mem_AΔ W hR 0
    have e : ps W 0 * (1 + (w : LetA O n) * W.π₀) = W.γA W.gam (qA W) := by
      rw [hγq]
      simp only [ps, pow_zero, AlgHom.one_apply]
    rw [e]
    exact gammaA_mem_AΔ_of_mem W W.gam hq
  intro t
  obtain ⟨U, hU⟩ := isUnit_one_add_mul_pi0 W hR (w : LetA O n)
  have hUm : (U : LetA O n) ∈ W.AΔ := by
    rw [hU]
    exact hu
  refine ⟨(W.φA ^ t) (U : LetA O n), phiA_pow_mem_AΔ W t hUm, (W.φA ^ t) (↑U⁻¹ : LetA O n),
    phiA_pow_mem_AΔ W t (mem_AΔ_of_mul_eq_one W hUm U.mul_inv), ?_, ?_⟩
  · rw [← map_mul, U.mul_inv, map_one]
  · show W.γA W.gam ((W.φA ^ t) (qA W)) = (W.φA ^ t) (U : LetA O n) * ps W t
    rw [γA_φpow, hγq, map_mul, hU]
    exact mul_comm _ _

theorem psUnitE_of [NeZero n] (W : LocWach PD LL O v n) (hR : RingP W) (hT : ToolsAlg W) : PsUnitE W := by
  intro s
  obtain ⟨-, h2, -, -⟩ := hT
  obtain ⟨u, P, hu, hm, hdeg, hdiv, hpS⟩ := h2 s
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hR
  have hb : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  show IsUnit (algebraMap (LetA O n) W.EE (pS W s))
  rw [hpS, map_mul, ← Polynomial.aeval_algebraMap_apply]
  refine (hu.map _).mul ?_
  obtain ⟨ub, hub⟩ := hb
  rw [← hub, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_smul]
  haveI := W.EE_complete
  have hz : (∑ i ∈ Finset.range P.natDegree, P.coeff i • (ub : W.EE) ^ i) ∈
      Ideal.span {((PD.p : ℕ) : W.EE)} := by
    refine Ideal.sum_mem _ (fun i hi => ?_)
    obtain ⟨d, hd⟩ := hdiv i (by rw [← hdeg]; exact Finset.mem_range.mp hi)
    rw [Ideal.mem_span_singleton, hd, Algebra.smul_def, map_mul, map_natCast, mul_assoc]
    exact dvd_mul_right _ _
  have hj := IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hz
  rw [Ideal.mem_jacobson_bot] at hj
  have hN : ((ub : W.EE) * (↑ub⁻¹ : W.EE)) ^ P.natDegree = 1 := by
    rw [Units.mul_inv, one_pow]
  have key : (∑ i ∈ Finset.range P.natDegree, P.coeff i • (ub : W.EE) ^ i) + (ub : W.EE) ^ P.natDegree
      = (ub : W.EE) ^ P.natDegree * ((∑ i ∈ Finset.range P.natDegree, P.coeff i • (ub : W.EE) ^ i) *
        (↑ub⁻¹ : W.EE) ^ P.natDegree + 1) := by
    linear_combination (-(∑ i ∈ Finset.range P.natDegree, P.coeff i • (ub : W.EE) ^ i)) * hN
  rw [key]
  exact (ub.isUnit.pow _).mul (hj _)

private lemma exists_phiA_pow_succ_pi0_eq_qA_mul (W : LocWach PD LL O v n) (hR : RingP W) (m : ℕ) :
    ∃ e : LetA O n, (W.φA ^ (m + 1)) W.π₀ = qA W * e := by
  obtain ⟨-, -, -, -, -, ⟨w, hw⟩, -⟩ := hR
  rw [Eat_X_add_p_pi0_eq_qA] at hw
  obtain ⟨k, hk⟩ : ∃ k, PD.p - 1 = k + 1 := ⟨PD.p - 2, by have := PD.hp.two_le; omega⟩
  have hA : ∀ j : ℕ, ∃ d : LetA O n, (W.φA ^ j) W.π₀ = W.π₀ * d := by
    intro j
    induction j with
    | zero => exact ⟨1, by simp⟩
    | succ j ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨(w : LetA O n) * qA W ^ (PD.p - 1) * W.φA d, ?_⟩
      rw [pow_succ', AlgHom.mul_apply, hd, map_mul, hw]
      ring
  obtain ⟨d, hd⟩ := hA m
  refine ⟨(w : LetA O n) * W.π₀ * qA W ^ k * W.φA d, ?_⟩
  rw [pow_succ', AlgHom.mul_apply, hd, map_mul, hw, hk]
  ring

private lemma exists_lA_eq_mul_ps_add_mul_ps_of_lt [IsDomain O] (W : LocWach PD LL O v n) (hR : RingP W) {s t : ℕ}
    (hst : s < t) : ∃ x ∈ W.AΔ, ∃ y ∈ W.AΔ, lA W ^ 1 = x * ps W s + y * ps W t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = s + (m + 1) := ⟨t - s - 1, by omega⟩
  obtain ⟨e, he⟩ := exists_phiA_pow_succ_pi0_eq_qA_mul W hR m
  have hφt : (W.φA ^ (s + (m + 1))) W.π₀ = ps W s * (W.φA ^ s) e := by
    show (W.φA ^ (s + (m + 1))) W.π₀ = (W.φA ^ s) (qA W) * (W.φA ^ s) e
    rw [pow_add, AlgHom.mul_apply, he, map_mul]
  have hc : (W.φA ^ s) e ∈ W.AΔ := by
    apply mem_AΔ_of_ps_mul_mem_AΔ W hR s
    rw [← hφt]
    exact phiA_pow_mem_AΔ W _ (pi0_mem_AΔ W hR)
  refine ⟨-(W.φA ^ s) e, neg_mem hc, 1, one_mem _, ?_⟩
  have hpt : ps W (s + (m + 1)) = (W.φA ^ (s + (m + 1))) W.π₀ + lA W := by
    simp only [ps, qA, lA, map_add, map_natCast]
  rw [hpt, hφt]
  ring

theorem psCoprime_of [IsDomain O] [NeZero n] (W : LocWach PD LL O v n) (hR : RingP W) :
    PsCoprime W := by
  intro s t hst
  refine ⟨1, ?_⟩
  rcases Nat.lt_or_gt_of_ne hst with h | h
  · exact exists_lA_eq_mul_ps_add_mul_ps_of_lt W hR h
  · obtain ⟨x, hx, y, hy, e⟩ := exists_lA_eq_mul_ps_add_mul_ps_of_lt W hR h
    exact ⟨y, hy, x, hx, by rw [e, add_comm]⟩

end Formalism.MainNotions.UnusedSlot80.KF
