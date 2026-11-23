import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultMk

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Mk

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem mono_two (v1 v2 : VarH X) (a b : ℕ) :
    (monomial (Finsupp.single v1 a + Finsupp.single v2 b) (1 : KK O) : RHH O X) =
      MvPolynomial.X v1 ^ a * MvPolynomial.X v2 ^ b := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

theorem softMk (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (C0 CE1 CE2 : ℝ) (a : IM X) :
    SoftOK S.w (fMk O C0 CE1 CE2 X a) (oMk C0 CE1 CE2 X a) (monomial (aMk C0 CE1 CE2 X a) 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · have h := softKSP S hS hD x.1 x.2 ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
    rw [sgKS_powP] at h
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)) 1) _
    rw [mono_two]
    exact h
  · have h := softKW S hS hD x.1 x.2.1 x.2.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softKS S hS hD x.1 x.2
    show SoftOK S.w _ _ (monomial (Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1) 1) _
    rw [mono_two, pow_one]
    exact h
  · have h := softLoc S.w hD h2 c
    show SoftOK S.w _ _ (monomial (∑ j : Fin (numSeg X.TT),
      Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)) 1) _
    rw [monomial_sum_one]
    have e : ∏ j : Fin (numSeg X.TT), (monomial (Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1)))
        (X.p ^ segG X.TT j - 1)) (1 : KK O) : RHH O X) = sgLoc O X := by
      unfold sgLoc
      exact Finset.prod_congr rfl fun j _ => by rw [X_pow_eq_monomial]
    rw [e]
    exact h

theorem fMk_pol (C0 CE1 CE2 : ℝ) (a : IM X) :
    fMk O C0 CE1 CE2 X a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgMk C0 CE1 CE2 X a) := by
  rcases a with x | x | x | c
  · exact mem_Pol_iff.2 fun l => by
      have h := (mem_Pol_iff.1 (kS_pol (O := O) x.1 x.2) l).pow ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
      rw [smul_eq_mul] at h
      exact h
  · exact kW_pol x.1 x.2.1 _
  · exact kS_pol x.1 x.2
  · exact loc_pol _

end Mk

section Deg

variable {X : Loc}

theorem topStart_inj (X : Loc) : Function.Injective (topStart X) := by
  intro j j' h
  have h1 : (evenTops X.TT).get j = (evenTops X.TT).get j' := congrArg Subtype.val h
  have hnd : (evenTops X.TT).Nodup := Finset.sort_nodup _ _
  exact hnd.get_inj_iff.mp h1

theorem topOdd_ne_endAny (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (j' : Fin (numSeg X.TT)) :
    topOdd X j i ≠ topEnd X j' := by
  intro h
  have h1 : (segPos X.TT j i).val = (segNext X.TT j').val := congrArg (fun x : X.TT => (x.val : ℕ)) h
  exact (pos_mem X.TT j i).2 (h1 ▸ (next_mem X.TT j').2)

theorem pd_le (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i ≤ X.p ^ segG X.TT j :=
  Nat.pow_le_pow_right hD.1.pos (dist_pos_lt X.TT j i).2.le

theorem dgMk_le (hD : D1num X) (hG : ∀ j, segG X.TT j ≤ X.G') (C0 CE1 CE2 : ℝ) (a : IM X) (l : X.TT × Bool) :
    dgMk C0 CE1 CE2 X a l ≤ X.p ^ X.G' := by
  have hp : 1 ≤ X.p := hD.1.one_lt.le
  have hpG : ∀ j, X.p ^ segG X.TT j ≤ X.p ^ X.G' := fun j => Nat.pow_le_pow_right hp (hG j)
  have h1 : 1 ≤ X.p ^ X.G' := Nat.one_le_pow _ _ hp
  have hdl : ∀ j i, X.p ^ (segDists X.TT j).get i ≤ X.p ^ X.G' := fun j i => (pd_le hD j i).trans (hpG j)
  have hso : ∀ j i, topStart X j ≠ topOdd X j i := by
    intro j i h
    have h2 : (segStart X.TT j).val = (segPos X.TT j i).val := congrArg (fun x : X.TT => (x.val : ℕ)) h
    exact (pos_mem X.TT j i).2 (h2 ▸ (start_mem X.TT j).2)
  rcases a with x | x | x | x
  · obtain ⟨-, hdG⟩ := dist_pos_lt X.TT x.1 x.2
    have hPd : (X.seg C0 CE1 CE2 x.1).P X.p x.2 * X.p ^ (segDists X.TT x.1).get x.2 = X.p ^ segG X.TT x.1 := by
      show X.p ^ (segG X.TT x.1 - (segDists X.TT x.1).get x.2) * _ = _
      rw [← pow_add, Nat.sub_add_cancel hdG.le]
    have hPle : (X.seg C0 CE1 CE2 x.1).P X.p x.2 ≤ X.p ^ segG X.TT x.1 := by
      rw [← hPd]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · rw [mul_one, add_zero, hPd]
      exact hpG _
    · rw [mul_zero, zero_add, mul_one]
      exact hPle.trans (hpG _)
    · simp
  · simp only [dgMk, dgKW, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp [Ne.symm (hso x.1 x.2.1)])
    · simpa using h1
    · simpa using hdl x.1 x.2.1
    · simp
  · simp only [dgMk, dgKS, dX]
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) (by simp)
    · simpa using hdl x.1 x.2
    · simpa using h1
    · simp
  · simp only [dgMk, dgLoc, dX]
    by_cases hex : ∃ j0, (topStart X j0, true) = l
    · obtain ⟨j0, hj0⟩ := hex
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0, mul_one]
        exact (Nat.sub_le _ _).trans (hpG j0)
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        apply hj
        apply topStart_inj X
        rw [← hj0] at h
        exact (Prod.mk.inj h).1
      · intro h
        exact absurd (Finset.mem_univ j0) h
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j _
        rw [if_neg (fun h => hex ⟨j, h⟩), mul_zero]

theorem dgMk_Y (C0 CE1 CE2 : ℝ) (a : IM X) (j' : Fin (numSeg X.TT)) : dgMk C0 CE1 CE2 X a (topEnd X j', false) = 0 := by
  rcases a with x | x | x | x <;>
    simp [dgMk, dgKS, dgKW, dgLoc, dX, topOdd_ne_endAny]

end Deg

section Sums

variable {X : Loc}

theorem bMk_eq (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    (∑ i : Fin (segS X.TT j), (β j).sg i • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j) +
        Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, (β j).rz i c.succ • ((Finsupp.single ((topOdd X j i, true), c.succ) 1 +
        Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) : MonH X))) +
    ((∑ i : Fin (segS X.TT j), (β j).ry i 0 • ((Finsupp.single ((topStart X j, true), 0) (X.p ^ (segDists X.TT j).get i) +
        Finsupp.single ((topOdd X j i, false), 0) 1 : MonH X))) +
      Finsupp.single ((topStart X j, true), 0) (X.c * (X.m * (X.p ^ segG X.TT j - 1))))) = bMk C0 CE1 CE2 X β j := by
  unfold bMk
  simp only [Finsupp.single_add, smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  ext k
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  by_cases hs : ((topStart X j, true), (0 : Fin (X.m + 1))) = k
  · subst hs
    simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Fin.succ_ne_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf
  · simp only [hs, if_false, Finset.sum_const_zero, zero_add, add_zero]
    try simp only [mul_comm, mul_left_comm]
    try abel
    try ring_nf

theorem sum_aMk (C0 CE1 CE2 : ℝ) (β : GlobalTheory X) :
    ∑ a, multMk X β a • aMk C0 CE1 CE2 X a = ∑ j, bMk C0 CE1 CE2 X β j := by
  simp only [← bMk_eq C0 CE1 CE2 β, Finset.sum_add_distrib]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
    rfl
  congr 1
  · rw [Fintype.sum_sigma]
    rfl
  · simp only [multMk, aMk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ring

end Sums

end Formalism.MainNotions.ColumnSystems.Pf
