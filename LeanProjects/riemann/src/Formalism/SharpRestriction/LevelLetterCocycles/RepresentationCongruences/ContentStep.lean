import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FormalSeriesValueAtTwoPointsGenericPoints

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo

open PowerSeries

section Pure

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

def deA (l b₀ y : ℕ) : ℕ :=
  (b₀ / l + 1) - min (b₀ / l + 1) (y - 1) + padicValNat l ((b₀ / l + 1).choose (min (b₀ / l + 1) (y - 1)))

theorem expand (l a : ℕ) {P Q w ε : O⟦X⟧} (hP : P = C (l : O) * ε + w * Q ^ l) (x : O) :
    C x * (w * Q ^ l) ^ a =
      ∑ i ∈ Finset.range (a + 1), (-ε) ^ (a - i) * C (x * ((a.choose i : O) * (l : O) ^ (a - i))) * P ^ i := by
  have hw : w * Q ^ l = P + (-(C (l : O) * ε)) := by rw [hP]; ring
  rw [hw, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem content_div {l : ℕ} [hlp : Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {P Q w ε U₀ U₁ : O⟦X⟧} (hε : IsUnit ε)
    (hP : P = C (l : O) * ε + w * Q ^ l) (hPd : IsDist P) (hPw : 1 ≤ wdeg P) (b₀ y κ : ℕ) (hy : 1 ≤ y)
    (x : O) (heq : C (l : O) ^ κ * U₀ - Q ^ b₀ * C x = P ^ y * U₁) :
    ∃ x' : O, x = (l : O) ^ (κ - deA l b₀ y) * x' := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, mul_zero]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, hv⟩ := ContPA.l_unit_mul hϖ hl0
  set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat with hE
  set a := b₀ / l + 1 with ha
  set i₀ := min a (y - 1) with hi₀
  have hla : b₀ ≤ l * a := by
    have h1 := Nat.div_add_mod b₀ l
    have h2 := Nat.mod_lt b₀ hlp.out.pos
    rw [ha, mul_add, mul_one]; omega
  have hmem : C x * (w * Q ^ l) ^ a ∈ Ideal.span {P ^ y, C ϖ ^ (E * κ)} := by
    have h1 : Q ^ b₀ * C x ∈ Ideal.span {P ^ y, C ϖ ^ (E * κ)} := by
      have e : Q ^ b₀ * C x = C ((v : O) ^ κ) * C ϖ ^ (E * κ) * U₀ - P ^ y * U₁ := by
        rw [← heq, hv]; simp only [map_mul, map_pow]; ring
      rw [e]
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))) (Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_insert _ _)))
    have h2 : C x * (w * Q ^ l) ^ a = w ^ a * Q ^ (l * a - b₀) * (Q ^ b₀ * C x) := by
      have hsplit : Q ^ (l * a) = Q ^ (l * a - b₀) * Q ^ b₀ := by rw [← pow_add, Nat.sub_add_cancel hla]
      rw [mul_pow, ← pow_mul, hsplit]; ring
    rw [h2]; exact Ideal.mul_mem_left _ _ h1
  rw [expand l a hP x] at hmem
  have hu : ∀ i ∈ Finset.range (a + 1), IsUnit ((-ε) ^ (a - i)) := fun i _ => hε.neg.pow _
  have hc : ∀ i ∈ Finset.range (a + 1), x * ((a.choose i : O) * (l : O) ^ (a - i)) ≠ 0 := by
    intro i hi
    exact mul_ne_zero hx0 (ContPA.coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  have key := (Mprime hϖ hPd hPw (Finset.range (a + 1)) (fun i => (-ε) ^ (a - i)) hu
    (fun i => x * ((a.choose i : O) * (l : O) ^ (a - i))) hc y (E * κ)).mp hmem i₀
    (Finset.mem_range.mpr (by omega)) (by omega)
  rw [IsDiscreteValuationRing.addVal_mul, ContPA.addVal_coef hl hl0 (by omega : i₀ ≤ a)] at key
  have hde : deA l b₀ y = a - i₀ + padicValNat l (a.choose i₀) := rfl
  have hdiv : ϖ ^ (E * (κ - deA l b₀ y)) ∣ x := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one, hde]
    generalize IsDiscreteValuationRing.addVal O x = t at key ⊢
    generalize a - i₀ + padicValNat l (a.choose i₀) = D at key ⊢
    induction t using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      have k1 : E * κ ≤ m + E * D := by exact_mod_cast key
      have k2 : E * (κ - D) ≤ m := by
        by_cases hκ : κ ≤ D
        · rw [Nat.sub_eq_zero_of_le hκ, mul_zero]; exact Nat.zero_le _
        · have h3 : E * (κ - D) + E * D = E * κ := by rw [← mul_add, Nat.sub_add_cancel (by omega)]
          generalize E * (κ - D) = X₁ at h3 ⊢
          generalize E * D = X₂ at h3 k1
          generalize E * κ = X₃ at h3 k1
          omega
      exact_mod_cast k2
  obtain ⟨x', hx'⟩ := hdiv
  refine ⟨((v⁻¹ : Oˣ) : O) ^ (κ - deA l b₀ y) * x', ?_⟩
  have hvv : (v : O) ^ (κ - deA l b₀ y) * ((v⁻¹ : Oˣ) : O) ^ (κ - deA l b₀ y) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  rw [hx', hv]
  linear_combination (-(ϖ ^ (E * (κ - deA l b₀ y)) * x')) * hvv

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem deA_le {l : ℕ} [hlp : Fact l.Prime] (b₀ y : ℕ) (hy : 1 ≤ y) (hb : 1 ≤ b₀) :
    (deA l b₀ y : ℝ) ≤ max 0 ((b₀ : ℝ) / l - y + 2 + Real.logb l b₀) + 1 := by
  have hl2 : 2 ≤ l := hlp.out.two_le
  have hfl : ((b₀ / l : ℕ) : ℝ) ≤ (b₀ : ℝ) / l := Nat.cast_div_le
  have hlog0 : 0 ≤ Real.logb l b₀ :=
    Real.logb_nonneg (by exact_mod_cast (show 1 < l by omega)) (by exact_mod_cast hb)
  have hm := le_max_right (0 : ℝ) ((b₀ : ℝ) / l - y + 2 + Real.logb l b₀)
  have hm0 := le_max_left (0 : ℝ) ((b₀ : ℝ) / l - y + 2 + Real.logb l b₀)
  unfold deA
  set a := b₀ / l + 1 with ha
  have hab : a ≤ b₀ := Nat.div_lt_self (by omega) (by omega)
  rcases le_or_gt a (y - 1) with h | h
  · simp only [min_eq_left h, Nat.sub_self, Nat.choose_self, padicValNat.one, add_zero, Nat.cast_zero]
    linarith
  · rw [min_eq_right h.le]
    have hV : padicValNat l (a.choose (y - 1)) ≤ Nat.log l a := by
      rw [← Nat.factorization_def _ hlp.out]
      exact Nat.factorization_choose_le_log
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (show 1 < l by omega)
    have hb0 : (0 : ℝ) < b₀ := by exact_mod_cast (show 0 < b₀ by omega)
    have hlogV : ((Nat.log l a : ℕ) : ℝ) ≤ Real.logb l b₀ := by
      rw [Real.le_logb_iff_rpow_le hl1 hb0, Real.rpow_natCast]
      exact_mod_cast (Nat.pow_log_le_self l (Nat.succ_ne_zero _)).trans hab
    have hsub : ((a - (y - 1) : ℕ) : ℝ) ≤ (b₀ : ℝ) / l - y + 2 := by
      rw [Nat.cast_sub h.le, Nat.cast_sub (by omega : 1 ≤ y), ha]
      push_cast
      linarith
    have hVr : (padicValNat l (a.choose (y - 1)) : ℝ) ≤ Nat.log l a := by exact_mod_cast hV
    rw [Nat.cast_add]
    linarith

end Pure

section Rec

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem l_mem_max (W : LocWach PD LL O v n) [IsLocalRing O] (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : algebraMap O LL (↑u⁻¹ * ((PD.p : ℕ) : O)) = 1 := by
    rw [← hu, Units.inv_mul, map_one]
  have h2 := congrArg v h1
  rw [map_mul, AddValuation.map_mul, map_natCast, W.v_l, AddValuation.map_one] at h2
  have h3 := hO ↑u⁻¹
  generalize v (algebraMap O LL ↑u⁻¹) = x at h2 h3
  induction x using WithTop.recTopCoe with
  | top => simp at h2
  | coe q =>
    have h2' : q + 1 = 0 := by exact_mod_cast h2
    have h3' : (0 : ℚ) ≤ q := by exact_mod_cast h3
    linarith

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [FiniteDimensional Qp LL]

theorem letE_idem (c : ZMod n) : (letE (O := O) c : LetA O n) * letE c = letE c := by
  unfold letE
  first
  | (rw [← Pi.single_mul, mul_one])
  | (ext i; by_cases h : i = c <;> simp [Pi.single_apply, h])

theorem content_step (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (c : ZMod n) (b₀ y κ : ℕ) (hy : 1 ≤ y) (f : W.EE) (x : O)
    (h1 : InFr W c 1 (qA W ^ b₀) f)
    (h2 : InFr W c (ps W 1 ^ y) (qA W ^ b₀)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ x'' : O, InFr W c (ps W 1 ^ y) (qA W ^ b₀)
      (lE W (deA PD.p b₀ y) * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
  haveI : Fact PD.p.Prime := Fact.mk PD.hp
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  have hp0 := GS.p_ne_zero W
  have hlm := l_mem_max W hO
  obtain ⟨u₀, hu₀, e1⟩ := h1
  obtain ⟨u₁, hu₁, e2⟩ := h2
  have hlE : ∀ k : ℕ, algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
    intro k; simp [lA, lE]
  have hxE : ∀ z : O, algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) z) = algebraMap O W.EE z :=
    fun z => (IsScalarTower.algebraMap_apply O (LetA O n) W.EE z).symm
  have hlA : ∀ z : O, ∀ k : ℕ, algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ k * z) =
      lA W ^ k * algebraMap O (LetA O n) z := by
    intro z k; simp [lA, map_mul, map_pow, map_natCast]

  have hG : letE c * (lA W ^ κ * u₀ - qA W ^ b₀ * algebraMap O (LetA O n) x) =
      letE c * ps W 1 ^ y * u₁ := by
    apply W.EE_inj
    simp only [map_mul, map_sub, map_one, mul_one, hlE, hxE] at e1 e2 ⊢
    linear_combination e2 - lE W κ * e1

  have hGc := congrFun hG c
  have hLc : (letE (O := O) c : LetA O n) c = 1 := by simp [letE]
  have hlAc : (lA W) c = C ((PD.p : ℕ) : O) := by simp [lA]
  have hxc : (algebraMap O (LetA O n) x) c = C x := rfl
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hLc, one_mul, hlAc, hxc] at hGc

  obtain ⟨-, ⟨w, hw⟩, -, -⟩ := hR
  have hq : qA W c = W.π₀ c + C ((PD.p : ℕ) : O) := by simp [qA, lA]
  have hPc : ps W 1 c = (w : LetA O n) c * W.π₀ c * qA W c ^ (PD.p - 1) + C ((PD.p : ℕ) : O) := by
    rw [GS.ps_letter 1 c, pow_one, hw]; rfl
  have hp1 : 1 ≤ PD.p := PD.hp.one_lt.le
  have hQp : qA W c ^ PD.p = qA W c ^ (PD.p - 1) * qA W c := by
    rw [← pow_succ, Nat.sub_add_cancel hp1]
  have hP : ps W 1 c = C ((PD.p : ℕ) : O) * (1 - (w : LetA O n) c * qA W c ^ (PD.p - 1)) +
      (w : LetA O n) c * qA W c ^ PD.p := by
    rw [hPc, hQp]
    have hπ : W.π₀ c = qA W c - C ((PD.p : ℕ) : O) := by rw [hq]; ring
    rw [hπ]; ring
  have hcc0 : constantCoeff (W.π₀ c) = 0 := GS.π₀₁_cc (GS.ringData_of_caseA_of_p9 W hcase hP9)
  have hccq : constantCoeff (qA W c) = ((PD.p : ℕ) : O) := by
    rw [hq, map_add, hcc0, constantCoeff_C, zero_add]
  have hε : IsUnit (1 - (w : LetA O n) c * qA W c ^ (PD.p - 1)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, map_one, map_mul, map_pow, hccq]
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    rw [← IsLocalRing.mem_maximalIdeal]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hlm _ (by have := PD.hp.two_le; omega))
  have hPd : IsDist (ps W 1 c) := GS.dist_ps (GS.ringData_of_caseA_of_p9 W hcase hP9) 1 (GS.dist_φpow (GS.ringData_of_caseA_of_p9 W hcase hP9) 1) c
  have hPw : 1 ≤ wdeg (ps W 1 c) := by
    unfold wdeg
    have hne : ((ps W 1 c).map (IsLocalRing.residue O)).order ≠ ⊤ := by
      rw [Ne, order_eq_top]; exact hPd
    have hcc : constantCoeff ((ps W 1 c).map (IsLocalRing.residue O)) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        GS.ps_letter 1 c, map_add, GS.cc_φpow (GS.ringData_of_caseA_of_p9 W hcase hP9) 1 c, constantCoeff_C, zero_add]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hlm
    have h1 : 1 ≤ ((ps W 1 c).map (IsLocalRing.residue O)).order :=
      one_le_order_iff_constCoeff_eq_zero.2 hcc
    rw [← ENat.natCast_toNat hne] at h1
    exact_mod_cast h1
  obtain ⟨x', hx'⟩ := content_div hlm hp0 hε hP hPd hPw b₀ y κ hy x hGc

  by_cases hκ : κ ≤ deA PD.p b₀ y
  · refine ⟨((PD.p : ℕ) : O) ^ (deA PD.p b₀ y - κ) * x, lA W ^ (deA PD.p b₀ y - κ) * u₁,
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hu₁, ?_⟩
    have hsplit : lE W (deA PD.p b₀ y) = lE W (deA PD.p b₀ y - κ) * lE W κ := by
      rw [lE, lE, lE, ← pow_add, Nat.sub_add_cancel hκ]
    rw [← hxE, hlA, hsplit]
    simp only [map_mul, map_sub, map_one, mul_one, hlE, hxE] at e2 ⊢
    linear_combination lE W (deA PD.p b₀ y - κ) * e2
  · have hκ' : κ = (κ - deA PD.p b₀ y) + deA PD.p b₀ y := by omega
    have hLmem : (letE (O := O) c : LetA O n) ∈ W.AΔ := fun δ _ => GS.γA_letE W δ c
    have hsat : lA W ^ (κ - deA PD.p b₀ y) *
        (letE c * (lA W ^ deA PD.p b₀ y * u₀ - qA W ^ b₀ * algebraMap O (LetA O n) x')) =
        ps W 1 ^ y * (letE c * u₁) := by
      have hx'' : algebraMap O (LetA O n) x =
          lA W ^ (κ - deA PD.p b₀ y) * algebraMap O (LetA O n) x' := by rw [hx', hlA]
      rw [hx'', hκ', pow_add] at hG
      rw [Nat.add_sub_cancel] at hG
      linear_combination hG
    have hpi : ps W 1 ^ y ∈ PiPs W :=
      Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 1))) y
    obtain ⟨y', hy', hz⟩ := GS.sat_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) hp0 hpi
      (Subalgebra.mul_mem _ hLmem hu₁) _ hsat
    refine ⟨x', y', hy', ?_⟩
    have hid := congrArg (algebraMap (LetA O n) W.EE) (letE_idem (O := O) c)
    have hzE := congrArg (algebraMap (LetA O n) W.EE) hz
    simp only [map_mul, map_sub, map_one, map_pow, mul_one, hlE, hxE] at e1 hid hzE ⊢
    linear_combination lE W (deA PD.p b₀ y) * e1 +
      algebraMap (LetA O n) W.EE (letE c) * hzE -
      (lE W (deA PD.p b₀ y) * algebraMap (LetA O n) W.EE u₀ -
        algebraMap (LetA O n) W.EE (qA W) ^ b₀ * algebraMap O W.EE x') * hid

end Rec

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo
