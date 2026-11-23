import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.P2PowMemSpanCUniformizerPowP1PowMulXPow
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

structure PhiData (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) where
  φ : O⟦X⟧ →ₐ[O] O⟦X⟧
  u : O⟦X⟧
  hu : IsUnit u
  hl : (l : O) ∈ IsLocalRing.maximalIdeal O
  hl0 : (l : O) ≠ 0
  hφ0 : φ (X - C (l : O)) = u * (X - C (l : O)) * X ^ (l - 1)
  hred : ∀ f : O⟦X⟧, (φ f).map (IsLocalRing.residue O) =
    subst ((u * X ^ l).map (IsLocalRing.residue O)) (f.map (IsLocalRing.residue O))

variable {l : ℕ} [Fact l.Prime] (P : PhiData O l)

noncomputable def PhiData.eps : O⟦X⟧ := 1 - P.u * X ^ (l - 1)

noncomputable def PhiData.p (s : ℕ) : O⟦X⟧ := (P.φ : O⟦X⟧ → O⟦X⟧)^[s] X

noncomputable def eO (l : ℕ) : ℕ := (IsDiscreteValuationRing.addVal O (l : O)).toNat

theorem l_eq_unit_mul_pow {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) :
    ∃ v : Oˣ, (l : O) = v * ϖ ^ eO (O := O) l :=
  ContPA.l_unit_mul hϖ hl0

theorem span_C_l_pow {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) (s : ℕ) :
    Ideal.span {(C (l : O) : O⟦X⟧) ^ s} = Ideal.span {C ϖ ^ (eO (O := O) l * s)} := by
  obtain ⟨v, hv⟩ := l_eq_unit_mul_pow hϖ hl0
  have h1 : (C (l : O) : O⟦X⟧) ^ s = C ((v : O) ^ s) * C ϖ ^ (eO (O := O) l * s) := by
    rw [hv, pow_mul, map_mul, map_pow, map_pow, mul_pow, ← map_pow]
  rw [h1, Ideal.span_singleton_mul_left_unit (((Units.isUnit v).pow s).map C)]

theorem PhiData.isUnit_eps : IsUnit P.eps := by
  have hl : l - 1 ≠ 0 := by
    have := (Fact.out : l.Prime).two_le
    omega
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [PhiData.eps, zero_pow hl]

theorem PhiData.φ_C_l : P.φ (C (l : O)) = C (l : O) := by
  simp [map_natCast]

theorem PhiData.p_succ (s : ℕ) : P.p (s + 1) = P.φ (P.p s) := by
  simp only [PhiData.p, Function.iterate_succ_apply']

theorem PhiData.first_partial_unit_eq_exp : P.p 1 = C (l : O) * P.eps + P.u * X ^ l := by
  have h1 : P.p 1 = P.φ X := rfl
  have h2 : P.φ X = P.φ (X - C (l : O)) + C (l : O) := by rw [map_sub, P.φ_C_l]; ring
  rw [h1, h2, P.hφ0]
  unfold PhiData.eps
  have hl1 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ']; congr 1; have := (Fact.out : l.Prime).one_lt; omega
  rw [hl1]; ring

theorem PhiData.p_two_eq_l_mul_phi_eps_add_phi_u_mul : P.p 2 = C (l : O) * P.φ P.eps + P.φ P.u * P.p 1 ^ l := by
  have h : P.p 2 = P.φ (P.p 1) := rfl
  have h1 : P.p 1 = P.φ X := rfl
  rw [h]
  conv_lhs => rw [P.first_partial_unit_eq_exp]
  rw [map_add, map_mul, map_mul, map_pow, P.φ_C_l, ← h1]

theorem PhiData.map_p (s : ℕ) : ∃ w : (IsLocalRing.ResidueField O)⟦X⟧, IsUnit w ∧
    (P.p s).map (IsLocalRing.residue O) = w * X ^ (l ^ s) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have ha : HasSubst ((P.u * X ^ l).map (IsLocalRing.residue O)) := by
    rw [map_mul, map_pow, map_X]
    exact (HasSubst.X_pow hl).mul_right
  have hu' : IsUnit (P.u.map (IsLocalRing.residue O)) := P.hu.map _
  induction s with
  | zero =>
    exact ⟨1, isUnit_one, by simp [PhiData.p]⟩
  | succ s ih =>
    obtain ⟨w, hw, hmap⟩ := ih
    refine ⟨subst ((P.u * X ^ l).map (IsLocalRing.residue O)) w *
      (P.u.map (IsLocalRing.residue O)) ^ (l ^ s), ?_, ?_⟩
    · refine IsUnit.mul ?_ (hu'.pow _)
      have := hw.map (substAlgHom (R := IsLocalRing.ResidueField O) ha)
      rwa [coe_substAlgHom] at this
    · rw [P.p_succ, P.hred, hmap, subst_mul ha, subst_pow ha, subst_X ha, map_mul, map_pow,
        map_X, mul_pow, ← pow_mul, ← pow_succ']
      ring

theorem PhiData.isDist_p (s : ℕ) : IsDist (P.p s) := by
  obtain ⟨w, hw, h⟩ := P.map_p s
  show (P.p s).map (IsLocalRing.residue O) ≠ 0
  rw [h]
  exact mul_ne_zero hw.ne_zero (pow_ne_zero _ X_ne_zero)
theorem PhiData.wdeg_p (s : ℕ) : wdeg (P.p s) = l ^ s := by
  obtain ⟨w, hw, hs⟩ := P.map_p s
  exact (ContPA.dist_of_map_eq hw _ hs).2

theorem PhiData.p_one_mem_span_l_X_pow_l : P.p 1 ∈ Ideal.span {C (l : O), (X : O⟦X⟧) ^ l} := by
  rw [P.first_partial_unit_eq_exp]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
theorem PhiData.p2_mem_span_C_natCast_p1_pow_natCast : P.p 2 ∈ Ideal.span {C (l : O), P.p 1 ^ l} := by
  rw [P.p_two_eq_l_mul_phi_eps_add_phi_u_mul]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
theorem PhiData.p_two_mem_span_l_X_pow_l_sq : P.p 2 ∈ Ideal.span {C (l : O), (X : O⟦X⟧) ^ (l ^ 2)} := by
  have h := ContPA.p2_sub_mul_X_pow_mem_span_C_natCast P.first_partial_unit_eq_exp P.p_two_eq_l_mul_phi_eps_add_phi_u_mul
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have : P.p 2 = z * C (l : O) + (P.φ P.u * P.u ^ l) * X ^ (l ^ 2) := by rw [hz, sq]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

private theorem addVal_l_eq_eO (hl0 : (l : O) ≠ 0) :
    IsDiscreteValuationRing.addVal O (l : O) = (eO (O := O) l : ℕ∞) := by
  unfold eO
  rw [ENat.coe_toNat]
  rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]

private theorem addVal_natCast_eq_of_l_mem_maximalIdeal (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal O (n : O) = ((eO (O := O) l * padicValNat l n : ℕ) : ℕ∞) := by
  have hp : l.Prime := Fact.out
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hunit : IsUnit (m : O) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
    simp only [eq_intCast, Int.cast_natCast] at hab
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hmem)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  push_cast
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hunit, addVal_l_eq_eO hϖ hl0,
    padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm]
  simp [nsmul_eq_mul, mul_comm]

private theorem natCast_ne_zero_of_l_mem_maximalIdeal (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) : (n : O) ≠ 0 := by
  intro h
  have h2 := addVal_natCast_eq_of_l_mem_maximalIdeal hϖ hl hl0 n hn
  rw [h, IsDiscreteValuationRing.addVal_zero] at h2
  exact ENat.top_ne_coe _ h2

private theorem one_le_wdeg_p_one : 1 ≤ wdeg (P.p 1) := by
  obtain ⟨w, hw, h⟩ := P.map_p 1
  unfold wdeg
  rw [h, order_mul, ContM_order_unit hw, order_X_pow]
  simpa using (Fact.out : l.Prime).one_lt.le

theorem PhiData.E1 (a y : ℕ) (hy : 1 ≤ y) :
    cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ (l * a)) =
      ⨅ i ∈ Finset.range (min a (y - 1) + 1),
        ((eO (O := O) l * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  set V : O⟦X⟧ := ↑P.hu.unit⁻¹ with hVdef
  have hVU : V * P.u = 1 := P.hu.val_inv_mul
  have hV : IsUnit V := (P.hu.unit⁻¹).isUnit
  set W : O⟦X⟧ := -(V * P.eps) with hWdef
  have hW : IsUnit W := (hV.mul P.isUnit_eps).neg
  have hXl : (X : O⟦X⟧) ^ l = V * P.p 1 + W * C (l : O) := by
    rw [P.first_partial_unit_eq_exp, hWdef]
    linear_combination (-(X : O⟦X⟧) ^ l) * hVU
  set uu : ℕ → O⟦X⟧ := fun i => V ^ i * W ^ (a - i) with huu
  set cc : ℕ → O := fun i => (a.choose i : O) * (l : O) ^ (a - i) with hcc
  have hexp : (X : O⟦X⟧) ^ (l * a) =
      ∑ i ∈ Finset.range (a + 1), uu i * C (cc i) * P.p 1 ^ i := by
    rw [pow_mul, hXl, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [huu, hcc, map_mul, map_pow, map_natCast]
    ring
  have hu : ∀ i ∈ Finset.range (a + 1), IsUnit (uu i) :=
    fun i _ => (hV.pow _).mul (hW.pow _)
  have hc : ∀ i ∈ Finset.range (a + 1), cc i ≠ 0 := by
    intro i hi
    have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact mul_ne_zero (natCast_ne_zero_of_l_mem_maximalIdeal hϖ P.hl P.hl0 _ (Nat.choose_pos hia).ne') (pow_ne_zero _ P.hl0)
  rw [hexp, Mprime_cont hϖ (P.isDist_p 1) (one_le_wdeg_p_one P hϖ) _ uu hu cc hc y]
  have hset : (Finset.range (a + 1)).filter (fun x => x < y) =
      Finset.range (min a (y - 1) + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  refine iInf_congr fun i => iInf_congr fun hi => ?_
  have hia : i ≤ a := by
    have := Finset.mem_range.mp hi
    omega
  simp only [hcc]
  rw [IsDiscreteValuationRing.addVal_mul, addVal_natCast_eq_of_l_mem_maximalIdeal hϖ P.hl P.hl0 _ (Nat.choose_pos hia).ne',
    IsDiscreteValuationRing.addVal_pow, addVal_l_eq_eO hϖ P.hl0]
  push_cast
  simp only [nsmul_eq_mul]
  push_cast [hia]
  ring

theorem PhiData.cont_pow_X_pow_eq_zero_of_lt (y b : ℕ) (hy : 1 ≤ y) (hb : 1 ≤ b) (hlt : b < l * y) :
    cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b) = 0 :=
  ContPA.content_p1_pow_X_pow_eq_zero hϖ P.hl P.hu P.first_partial_unit_eq_exp y b hlt

theorem PhiData.content_p1_pow_X_pow_le (y b : ℕ) (hy : 1 ≤ y) (hb : 1 ≤ b) :
    cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b) ≠ ⊤ ∧
    ((cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b)).toNat : ℝ) ≤
      eO (O := O) l * max 0 ((b : ℝ) / l - y + 2 + Real.logb l b) := by
  unfold eO
  exact ContPA.content_p1_pow_X_pow_le_general hϖ P.hl P.hl0 P.isUnit_eps P.hu P.first_partial_unit_eq_exp y b hy hb

theorem PhiData.E2 (y be : ℕ) (hbe : 1 ≤ be) :
    cont ϖ ((X : O⟦X⟧) ^ (l * be)) (P.p 1 ^ y) =
      ⨅ i ∈ Finset.range (min y (be - 1) + 1),
        ((eO (O := O) l * (y - i + padicValNat l (y.choose i)) : ℕ) : ℕ∞) := by
  unfold eO
  exact ContPA.formalSeriesValueAtTwoPoints_genericPoints hϖ P.hl P.hl0 P.isUnit_eps P.hu P.first_partial_unit_eq_exp y be hbe

theorem PhiData.lineCoeffQuadratic_mem (B y : ℕ) (hB : 1 ≤ B) (hy : 1 ≤ y) :
    P.p 1 ^ y ∈ Ideal.span {C (l : O) ^ (y + 1 - (B + l - 1) / l), (X : O⟦X⟧) ^ B} :=
  ContPA.p1_pow_mem_span_C_pow_X_pow P.first_partial_unit_eq_exp y B

theorem PhiData.cont_X_pow_pow_eq_zero_of_gt (B y : ℕ) (hB : 1 ≤ B) (hy : 1 ≤ y) (hlt : l * y < B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y) = 0 :=
  ContPA.content_X_pow_p1_pow_eq_zero hϖ P.hl P.hu P.first_partial_unit_eq_exp B y hlt

theorem PhiData.constant_le_rpow_of_three_le (B y : ℕ) (hB : 1 ≤ B) (hy : 1 ≤ y) :
    cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y) ≠ ⊤ ∧
    ((cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat : ℝ) ≤
      eO (O := O) l * max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
  have hp : l.Prime := Fact.out
  have hlp : 0 < l := hp.pos
  set I := (Finset.range (y + 1)).image (fun j => l * j) with hI
  set uu : ℕ → O⟦X⟧ := fun i => P.u ^ (i / l) * P.eps ^ (y - i / l) with huu
  set cc : ℕ → O := fun i => (y.choose (i / l) : O) * (l : O) ^ (y - i / l) with hcc
  have hexp : P.p 1 ^ y = ∑ i ∈ I, uu i * C (cc i) * X ^ i := by
    rw [hI, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hlp h), P.first_partial_unit_eq_exp,
      add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [huu, hcc, Nat.mul_div_cancel_left j hlp, map_mul, map_pow, map_natCast]
    ring
  have hu : ∀ i ∈ I, IsUnit (uu i) := fun i _ => (P.hu.pow _).mul (P.isUnit_eps.pow _)
  have hc : ∀ i ∈ I, cc i ≠ 0 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have hjy : j ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [hcc, Nat.mul_div_cancel_left j hlp]
    exact mul_ne_zero (natCast_ne_zero_of_l_mem_maximalIdeal hϖ P.hl P.hl0 _ (Nat.choose_pos hjy).ne') (pow_ne_zero _ P.hl0)
  have hX : IsDist (X : O⟦X⟧) := by
    show (X : O⟦X⟧).map (IsLocalRing.residue O) ≠ 0
    rw [map_X]
    exact X_ne_zero
  have hwX : 1 ≤ wdeg (X : O⟦X⟧) := by
    unfold wdeg
    rw [map_X, order_X]
    simp
  have hcont := Mprime_cont hϖ hX hwX I uu hu cc hc B
  rw [← hexp] at hcont
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 = min y ((B - 1) / l) := ⟨_, rfl⟩
  have hj0y : j0 ≤ y := hj0 ▸ min_le_left _ _
  have hj0B : j0 ≤ (B - 1) / l := hj0 ▸ min_le_right _ _
  have hlj : l * j0 < B := by
    have h1 := Nat.mul_le_mul_left l hj0B
    have h2 := Nat.mul_div_le (B - 1) l
    omega
  have hmem : l * j0 ∈ I.filter (fun x => x < B) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_image.2 ⟨j0, Finset.mem_range.2 (Nat.lt_succ_of_le hj0y), rfl⟩, hlj⟩
  set v := padicValNat l (y.choose j0) with hv
  have hval : IsDiscreteValuationRing.addVal O (cc (l * j0)) =
      ((eO (O := O) l * (v + (y - j0)) : ℕ) : ℕ∞) := by
    simp only [hcc, Nat.mul_div_cancel_left j0 hlp]
    rw [IsDiscreteValuationRing.addVal_mul, addVal_natCast_eq_of_l_mem_maximalIdeal hϖ P.hl P.hl0 _ (Nat.choose_pos hj0y).ne',
      IsDiscreteValuationRing.addVal_pow, addVal_l_eq_eO hϖ P.hl0, ← hv, nsmul_eq_mul]
    norm_cast
    ring
  have hle : cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y) ≤
      ((eO (O := O) l * (v + (y - j0)) : ℕ) : ℕ∞) := by
    rw [hcont, ← hval]
    exact iInf₂_le (l * j0) hmem
  have hne : cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  refine ⟨hne, ?_⟩
  have htn : (cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat ≤ eO (O := O) l * (v + (y - j0)) := by
    have h := ENat.toNat_le_toNat hle (ENat.coe_ne_top _)
    rwa [ENat.toNat_coe] at h
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hlp
  have hbound : ((v + (y - j0) : ℕ) : ℝ) ≤ max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
    have hcase : j0 = y ∨ j0 = (B - 1) / l := by
      rw [hj0]
      exact min_choice _ _
    rcases hcase with h | h
    · have hv0 : v = 0 := by
        rw [hv, h, Nat.choose_self, padicValNat.one]
      rw [hv0, h, Nat.sub_self]
      simp
    · refine le_trans ?_ (le_max_right _ _)
      have hlog : (v : ℝ) ≤ Real.logb l y := by
        have h1 : v ≤ Nat.log l y := by
          rw [hv, ← Nat.factorization_def _ hp]
          exact Nat.factorization_choose_le_log
        exact le_trans (by exact_mod_cast h1) (Real.natLog_le_logb y l)
      have hBl : (B : ℝ) / l ≤ j0 + 1 := by
        have h1 := Nat.lt_mul_div_succ (B - 1) hlp
        rw [← h] at h1
        have h2 : B ≤ l * (j0 + 1) := by
          generalize l * (j0 + 1) = t at h1
          omega
        have h3 : (B : ℝ) ≤ l * (j0 + 1) := by exact_mod_cast h2
        rw [div_le_iff₀ hlpos]
        linarith
      push_cast [hj0y]
      linarith
  calc ((cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat : ℝ)
      ≤ ((eO (O := O) l * (v + (y - j0)) : ℕ) : ℝ) := by exact_mod_cast htn
    _ ≤ eO (O := O) l * max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)

private theorem le_eO_mul_of_l_ne_zero (hl0 : (l : O) ≠ 0) {k N : ℕ} (h : k ≤ eO (O := O) l * N) :
    (C ϖ : O⟦X⟧) ^ k ∣ (C (l : O)) ^ N := by
  obtain ⟨v, hv⟩ := l_eq_unit_mul_pow hϖ hl0
  have h1 : (C (l : O) : O⟦X⟧) ^ N = C ((v : O) ^ N) * C ϖ ^ (eO (O := O) l * N) := by
    rw [hv, pow_mul, map_mul, map_pow, map_pow, mul_pow, ← map_pow]
  rw [h1]
  exact dvd_mul_of_dvd_right (pow_dvd_pow _ h) _

private theorem le_mul_of_le_ceil_mul_of_le (x : ℝ) (k N e : ℕ) (hk : k ≤ ⌈(e : ℝ) * x⌉₊) (hx : x ≤ N) :
    k ≤ e * N := by
  have h : (e : ℝ) * x ≤ ((e * N : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
  exact hk.trans (Nat.ceil_le.2 h)

private theorem le_of_le_ceil_eO_mul (w B η k : ℕ)
    (hk : k ≤ ⌈(eO (O := O) l : ℝ) * ((w : ℝ) - B / l - η / (l : ℝ) ^ 2)⌉₊) :
    P.p 2 ^ w ∈ Ideal.span {C ϖ ^ k, P.p 1 ^ B * (X : O⟦X⟧) ^ η} := by
  set I := Ideal.span {C ϖ ^ k, P.p 1 ^ B * (X : O⟦X⟧) ^ η} with hI
  have hϖI : (C ϖ : O⟦X⟧) ^ k ∈ I := Ideal.subset_span (by simp)
  have hgI : P.p 1 ^ B * (X : O⟦X⟧) ^ η ∈ I := Ideal.subset_span (by simp)
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  set a : ℝ := (B : ℝ) / l with ha
  set b : ℝ := (η : ℝ) / (l : ℝ) ^ 2 with hb
  have hBa : (B : ℝ) = a * l := by rw [ha]; field_simp
  have hηb : (η : ℝ) = b * l ^ 2 := by rw [hb]; field_simp
  have hb0 : 0 ≤ b := by positivity
  have hkey : ∀ N : ℕ, (w : ℝ) - a - b ≤ N → C ϖ ^ k ∣ (C (l : O) : O⟦X⟧) ^ N :=
    fun N hN => le_eO_mul_of_l_ne_zero hϖ P.hl0 (le_mul_of_le_ceil_mul_of_le hϖ _ _ _ _ hk hN)
  rw [P.p_two_eq_l_mul_phi_eps_add_phi_u_mul, add_comm, add_pow]
  refine Ideal.sum_mem _ fun j hj => ?_
  have hjw : j ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hc : (j : ℝ) ≤ a + b
  · obtain ⟨q, hq⟩ := hkey (w - j) (by push_cast [hjw]; linarith)
    have e1 : (P.φ P.u * P.p 1 ^ l) ^ j * (C (l : O) * P.φ P.eps) ^ (w - j) *
        ((w.choose j : ℕ) : O⟦X⟧) =
        C ϖ ^ k * (q * ((P.φ P.u * P.p 1 ^ l) ^ j * P.φ P.eps ^ (w - j) *
          ((w.choose j : ℕ) : O⟦X⟧))) := by
      rw [mul_pow (C (l : O)), hq]
      ring
    rw [e1]
    exact I.mul_mem_right _ hϖI
  · push_neg at hc
    have hBj : B ≤ l * j := by
      have h2 : (B : ℝ) < l * j := by
        rw [hBa]
        nlinarith
      exact_mod_cast h2.le
    set N := l * j - B with hN
    have hsplit : P.p 1 ^ (l * j) = P.p 1 ^ B * P.p 1 ^ N := by
      rw [← pow_add, hN, Nat.add_sub_cancel' hBj]
    have hexp : P.p 1 ^ N = ∑ m ∈ Finset.range (N + 1),
        (P.u * X ^ l) ^ m * (C (l : O) * P.eps) ^ (N - m) * ((N.choose m : ℕ) : O⟦X⟧) := by
      rw [P.first_partial_unit_eq_exp, add_comm, add_pow]
    have e2 : (P.φ P.u * P.p 1 ^ l) ^ j * (C (l : O) * P.φ P.eps) ^ (w - j) *
        ((w.choose j : ℕ) : O⟦X⟧) = ∑ m ∈ Finset.range (N + 1),
          P.p 1 ^ B * X ^ (l * m) * (P.φ P.u ^ j * P.u ^ m * (C (l : O) * P.eps) ^ (N - m) *
            ((N.choose m : ℕ) : O⟦X⟧) * (C (l : O) * P.φ P.eps) ^ (w - j) *
            ((w.choose j : ℕ) : O⟦X⟧)) := by
      rw [mul_pow, ← pow_mul, hsplit, hexp, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_pow P.u, ← pow_mul]
      ring
    rw [e2]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    by_cases hη : η ≤ l * m
    · have e3 : P.p 1 ^ B * (X : O⟦X⟧) ^ (l * m) = (P.p 1 ^ B * X ^ η) * X ^ (l * m - η) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hη]
      rw [e3, mul_assoc]
      exact I.mul_mem_right _ hgI
    · push_neg at hη
      have hmr : (l : ℝ) * m < η := by exact_mod_cast hη
      have hcast : ((N - m : ℕ) : ℝ) = (l : ℝ) * j - B - m := by
        rw [Nat.cast_sub hmN, hN, Nat.cast_sub hBj]
        push_cast
        ring
      obtain ⟨q, hq⟩ := hkey (N - m + (w - j)) (by
        rw [Nat.cast_add, hcast, Nat.cast_sub hjw, hBa]
        rw [hηb] at hmr
        have hm' : (m : ℝ) ≤ b * l := by nlinarith
        have h3 : ((l : ℝ) - 1) * b ≤ ((l : ℝ) - 1) * (j - a) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith)
      have e4 : P.p 1 ^ B * X ^ (l * m) * (P.φ P.u ^ j * P.u ^ m * (C (l : O) * P.eps) ^ (N - m) *
          ((N.choose m : ℕ) : O⟦X⟧) * (C (l : O) * P.φ P.eps) ^ (w - j) *
          ((w.choose j : ℕ) : O⟦X⟧)) =
          C ϖ ^ k * (q * (P.p 1 ^ B * X ^ (l * m) * P.φ P.u ^ j * P.u ^ m * P.eps ^ (N - m) *
            ((N.choose m : ℕ) : O⟦X⟧) * P.φ P.eps ^ (w - j) * ((w.choose j : ℕ) : O⟦X⟧))) := by
        rw [← mul_assoc (C ϖ ^ k) q, ← hq, pow_add]
        ring
      rw [e4]
      exact I.mul_mem_right _ hϖI

theorem PhiData.c3a (y B : ℕ) (hB : 1 ≤ B) (k : ℕ)
    (hk : k ≤ ⌈(eO (O := O) l : ℝ) * ((y : ℝ) - B / (l : ℝ) ^ 2)⌉₊) :
    P.p 2 ^ y ∈ Ideal.span {C ϖ ^ k, (X : O⟦X⟧) ^ B} := by
  have h := le_of_le_ceil_eO_mul P hϖ y 0 B k (by simpa using hk)
  simpa using h

theorem PhiData.c3b (w B η : ℕ) (hBη : 1 ≤ B ∨ 1 ≤ η) (k : ℕ)
    (hk : k ≤ ⌈(eO (O := O) l : ℝ) * ((w : ℝ) - B / l - η / (l : ℝ) ^ 2)⌉₊) :
    P.p 2 ^ w ∈ Ideal.span {C ϖ ^ k, P.p 1 ^ B * (X : O⟦X⟧) ^ η} := by
  exact le_of_le_ceil_eO_mul P hϖ w B η k hk

end Formalism.MainNotions.N.FrobeniusPowerSeries
