import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IntBinomScalar
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.VeluIntegral

noncomputable section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

namespace USideB

section SlopeTestRemainingChoices

variable {K : Type} [Field K]

theorem hs_of {a : PowerSeries K} (h : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero' h

theorem cc_subst {a f : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem cc_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.constantCoeff (mulBy l linv al) = 0 := by
  exact cc_subst (by simp [h.1]) h.2.2.1

theorem subst_mulBy_l {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have hb : PowerSeries.constantCoeff (PowerSeries.C al * l) = 0 := by simp [h.1]
  rw [mulBy, ← PowerSeries.subst_comp_subst_apply (hs_of h.2.2.1) (hs_of hb), h.2.2.2.2,
    PowerSeries.subst_X (hs_of hb)]

theorem subst_rescale {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    PowerSeries.subst l (PowerSeries.rescale al g) =
      PowerSeries.subst (mulBy l linv al) (PowerSeries.subst l g) := by
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hs : PowerSeries.HasSubst (al • PowerSeries.X : PowerSeries K) := hs_of (by simp)
  rw [PowerSeries.subst_comp_subst_apply hl (hs_of (cc_mulBy h al)), subst_mulBy_l h al,
    PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hs hl,
    PowerSeries.subst_smul hl, PowerSeries.subst_X hl, PowerSeries.smul_eq_C_mul]

theorem l_ne_zero {l linv : PowerSeries K} (h : IsLogPair l linv) : l ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0] at h1
  simp at h1

theorem subst_wpShift {e l A : PowerSeries K} {c0 : K} (hl : PowerSeries.constantCoeff l = 0)
    (hX : XIsWp e l A c0) (x : K) :
    PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e (x + c0)) =
      (A - PowerSeries.C x * PowerSeries.X ^ 2) * l ^ 2 := by
  have hs := hs_of hl
  have e1 : wpShift e (x + c0) = wpShift e 0 - PowerSeries.C (x + c0) * PowerSeries.X ^ 2 := by
    simp only [wpShift, map_zero, sub_zero]
    ring
  have e2 : PowerSeries.subst l (wpShift e (x + c0)) =
      PowerSeries.subst l (wpShift e 0) - PowerSeries.C (x + c0) * l ^ 2 := by
    rw [e1, PowerSeries.subst_sub hs, PowerSeries.subst_mul hs, PowerSeries.subst_C,
      PowerSeries.subst_pow hs, PowerSeries.subst_X hs]
    rfl
  rw [e2, mul_sub, ← hX, map_add]
  ring

end SlopeTestRemainingChoices

section FormalExponential

variable {K : Type} [Field K] [CharZero K]

theorem mvExp_pow (hE : MvExpLaws) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0)
    (m : ℕ) : (mvExp f : PowerSeries K) ^ m = mvExp ((m : K) • f) := by
  obtain ⟨L0, -, L2, -⟩ := hE K Unit
  induction m with
  | zero => simp [L0]
  | succ m ih =>
    have hc : PowerSeries.constantCoeff ((m : K) • f) = 0 := by simp [hf]
    rw [pow_succ, ih, ← L2 _ _ hc hf]
    congr 1
    push_cast
    rw [add_smul, one_smul]

end FormalExponential

end USideB

open USideB

section Main

theorem isogenyU_of (hE : MvExpLaws) (hS : MvExpSubst) : IsogenyU := by
  intro K _ _ e s2 l linv ph A c0 ι _ xP al h hph hX hI
  set m := mulBy l linv al with hmdef
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hmc : PowerSeries.constantCoeff m = 0 := cc_mulBy h al
  have hms : PowerSeries.HasSubst m := hs_of hmc
  have hneg : ∀ f : PowerSeries K, PowerSeries.subst m (-f) = -PowerSeries.subst m f := by
    intro f
    rw [← PowerSeries.coe_substAlgHom hms, map_neg]

  have k1 : PowerSeries.subst l (PowerSeries.rescale al (sgStar e s2)) =
      m * mvExp (-(PowerSeries.subst m ph)) := by
    rw [subst_rescale h al, ← hph.2, PowerSeries.subst_mul hms, PowerSeries.subst_X hms,
      hS K Unit (-ph) m (by simp [hph.1]) hmc, hneg]
  have key := congrArg (PowerSeries.substAlgHom hl) hI
  simp only [map_mul, map_pow, map_prod, PowerSeries.coe_substAlgHom] at key
  rw [k1, PowerSeries.subst_X hl, PowerSeries.subst_C, ← hph.2] at key
  have hC : (MvPowerSeries.C al : PowerSeries K) = PowerSeries.C al := rfl
  rw [hC] at key

  have hprod : PowerSeries.X ^ (2 * Fintype.card ι) *
      ∏ P, PowerSeries.subst l (wpShift e (xP P + c0)) =
      (∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)) * l ^ (2 * Fintype.card ι) := by
    calc PowerSeries.X ^ (2 * Fintype.card ι) * ∏ P, PowerSeries.subst l (wpShift e (xP P + c0))
        = (∏ _P : ι, (PowerSeries.X : PowerSeries K) ^ 2) *
            ∏ P, PowerSeries.subst l (wpShift e (xP P + c0)) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      _ = ∏ P, (PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e (xP P + c0))) :=
          Finset.prod_mul_distrib.symm
      _ = ∏ P, ((A - PowerSeries.C (xP P) * PowerSeries.X ^ 2) * l ^ 2) :=
          Finset.prod_congr rfl fun P _ => subst_wpShift h.1 hX (xP P)
      _ = (∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)) * ∏ _P : ι, l ^ 2 :=
          Finset.prod_mul_distrib
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have p1 : (mvExp (-(PowerSeries.subst m ph)) : PowerSeries K) ^ 2 =
      mvExp (-((2 : K) • PowerSeries.subst m ph)) := by
    rw [mvExp_pow hE (by rw [map_neg, cc_subst hmc hph.1, neg_zero]) 2]
    congr 1
    rw [smul_neg]
    norm_num
  have p2 : (mvExp (-ph) : PowerSeries K) ^ (2 * (Fintype.card ι + 1)) =
      mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph)) := by
    rw [mvExp_pow hE (by rw [map_neg, hph.1, neg_zero]) _]
    congr 1
    rw [smul_neg]
    push_cast
    rfl
  apply mul_right_cancel₀ (pow_ne_zero (2 * Fintype.card ι) (l_ne_zero h))
  rw [← p1, ← p2, map_pow]
  linear_combination PowerSeries.X ^ (2 * Fintype.card ι) * key +
    PowerSeries.C al ^ 2 * PowerSeries.X ^ (2 * (Fintype.card ι + 1)) *
      (mvExp (-ph) : PowerSeries K) ^ (2 * (Fintype.card ι + 1)) * hprod

end Main

namespace USideB

section Integral

variable {K : Type} [Field K]

def intSub (R : Subring K) : Subring (PowerSeries K) where
  carrier := {f | IntPS R f}
  mul_mem' := by
    intro f g hf hg n
    rw [PowerSeries.coeff_mul]
    exact R.sum_mem fun p _ => R.mul_mem (hf _) (hg _)
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  add_mem' := by
    intro f g hf hg n
    rw [map_add]
    exact R.add_mem (hf _) (hg _)
  zero_mem' := by
    intro n
    rw [map_zero]
    exact R.zero_mem
  neg_mem' := by
    intro f hf n
    rw [map_neg]
    exact R.neg_mem (hf _)

theorem mem_intSub {R : Subring K} {f : PowerSeries K} : f ∈ intSub R ↔ IntPS R f := Iff.rfl

theorem C_mem_intSub {R : Subring K} {a : K} (ha : a ∈ R) : PowerSeries.C a ∈ intSub R := by
  refine mem_intSub.2 fun n => ?_
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem

theorem X_mem_intSub (R : Subring K) : (PowerSeries.X : PowerSeries K) ∈ intSub R := by
  refine mem_intSub.2 fun n => ?_
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem int_of_mul {R : Subring K} {U V W : PowerSeries K} (hU : IsOneUnit R U) (hW : IntPS R W)
    (h : V * U = W) : IntPS R V := by
  have h0 : PowerSeries.coeff 0 U = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hU.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Nat.sub_self, h0, mul_one] at hc

    have hn : PowerSeries.coeff n V = PowerSeries.coeff n W -
        ∑ k ∈ Finset.range n, PowerSeries.coeff k V * PowerSeries.coeff (n - k) U := by
      rw [← hc]
      ring
    rw [hn]
    exact R.sub_mem (hW n)
      (R.sum_mem fun k hk => R.mul_mem (ih k (Finset.mem_range.1 hk)) (hU.2 _))

theorem intMv_of_intPS {R : Subring K} {f : PowerSeries K} (h : IntPS R f) :
    IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun x => by cases x; simp
  rw [e]
  exact h (n ())

end Integral

end USideB

section Main2

theorem phNormUnit_of (hE : MvExpLaws) (_hS : MvExpSubst) (hH : LGHalf) (hU : IsogenyU) :
    PhNormUnit := by
  intro K _ _ R e s2 l linv ph A c0 ι _ xP al h hph hX hI hA hxP hal hali hal0 h2 hm
  obtain ⟨L0, L1, L2, -⟩ := hE K Unit
  have mvc : ∀ f : PowerSeries K, PowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (f : MvPowerSeries Unit K) = 0 := fun f hf => hf
  have hiso := hU K e s2 l linv ph A c0 ι xP al h hph hX hI
  have hmc : PowerSeries.constantCoeff (mulBy l linv al) = 0 := cc_mulBy h al
  have hsc : PowerSeries.constantCoeff (PowerSeries.subst (mulBy l linv al) ph) = 0 :=
    cc_subst hmc hph.1
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.2 hmc
  set k := Fintype.card ι with hk
  set s := PowerSeries.subst (mulBy l linv al) ph with hs
  set D : PowerSeries K := s - ((k : K) + 1) • ph with hD
  set Q := ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2) with hQ
  set E1 : PowerSeries K := mvExp (-((2 : K) • s)) with hE1
  set E2 : PowerSeries K := mvExp (-((2 * ((k : K) + 1)) • ph)) with hE2
  set F : PowerSeries K := mvExp ((2 * ((k : K) + 1)) • ph) with hF
  rw [hu] at hiso hm

  have h1 : u ^ 2 * E1 = PowerSeries.C (al ^ 2) * E2 * Q := by
    apply mul_left_cancel₀ (pow_ne_zero (2 * (k + 1)) (PowerSeries.X_ne_zero (R := K)))
    linear_combination hiso
  have cE1 : PowerSeries.constantCoeff E1 = 1 := L1 _ (mvc _ (by simp [hsc]))
  have cE2 : PowerSeries.constantCoeff E2 = 1 := L1 _ (mvc _ (by simp [hph.1]))
  have cQ : PowerSeries.constantCoeff Q = 1 := by simp [hQ, map_prod, hA.1]
  have cu : PowerSeries.constantCoeff u ^ 2 = al ^ 2 := by
    have h3 := congrArg PowerSeries.constantCoeff h1
    simpa [cE1, cE2, cQ] using h3
  have hu_int : IntPS R u := by
    intro n
    have h4 := hm (n + 1)
    rwa [PowerSeries.coeff_succ_X_mul] at h4
  set v := PowerSeries.C al⁻¹ * u with hv
  have hv1 : IsOneUnit R (v ^ 2) := by
    constructor
    · rw [map_pow, hv, map_mul, PowerSeries.constantCoeff_C, mul_pow, cu, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 2 hal0)]
    · exact mem_intSub.1 (pow_mem (mul_mem (C_mem_intSub hali) (mem_intSub.2 hu_int)) 2)
  have cph : PowerSeries.constantCoeff ((2 * ((k : K) + 1)) • ph) = 0 := by simp [hph.1]
  have cs2 : PowerSeries.constantCoeff (-((2 : K) • s)) = 0 := by simp [hsc]
  have hEF : E2 * F = 1 := by
    rw [hE2, hF, ← L2 _ _ (mvc _ (by simp [hph.1])) (mvc _ cph), neg_add_cancel, L0]
  have hDD : (mvExp (-(D + D)) : PowerSeries K) = E1 * F := by
    rw [hE1, hF, ← L2 _ _ (mvc _ cs2) (mvc _ cph)]
    congr 1
    rw [hD]
    module

  have hkey : (mvExp (-(D + D)) : PowerSeries K) * v ^ 2 = Q := by
    rw [hDD]
    have hv2 : v ^ 2 = PowerSeries.C al⁻¹ ^ 2 * u ^ 2 := by rw [hv, mul_pow]
    calc E1 * F * v ^ 2 = PowerSeries.C al⁻¹ ^ 2 * F * (u ^ 2 * E1) := by rw [hv2]; ring
      _ = PowerSeries.C al⁻¹ ^ 2 * F * (PowerSeries.C (al ^ 2) * E2 * Q) := by rw [h1]
      _ = PowerSeries.C (al⁻¹ ^ 2 * al ^ 2) * (E2 * F) * Q := by simp only [map_mul, map_pow]; ring
      _ = Q := by rw [hEF, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hal0), map_one]; ring
  have hAm : A ∈ intSub R := mem_intSub.2 hA.2
  have hQi : IntPS R Q := mem_intSub.1 (prod_mem fun P _ =>
    sub_mem hAm (mul_mem (C_mem_intSub (hxP P)) (pow_mem (X_mem_intSub R) 2)))
  have hI1 : IntPS R (mvExp (-(D + D)) : PowerSeries K) := int_of_mul hv1 hQi hkey
  have cD : PowerSeries.constantCoeff D = 0 := by simp [hD, hsc, hph.1]
  have cDD : PowerSeries.constantCoeff (D + D) = 0 := by simp [cD]
  have cnDD : PowerSeries.constantCoeff (-(D + D)) = 0 := by simp [cD]
  have hone : IsOneUnit R (mvExp (-(D + D)) : PowerSeries K) := ⟨L1 _ (mvc _ cnDD), hI1⟩
  have hinv : (mvExp (D + D) : PowerSeries K) * mvExp (-(D + D)) = 1 := by
    rw [← L2 _ _ (mvc _ cDD) (mvc _ cnDD), add_neg_cancel, L0]
  have hI2 : IntPS R (mvExp (D + D) : PowerSeries K) :=
    int_of_mul hone (mem_intSub.1 (one_mem _)) hinv
  exact hH K R Unit h2 D ⟨mvc _ cDD, intMv_of_intPS hI2⟩

end Main2

end Formalism.L2.Th1.C
