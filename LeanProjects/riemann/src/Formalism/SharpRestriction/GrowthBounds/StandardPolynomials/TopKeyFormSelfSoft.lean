import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section H

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

def hTop (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) : RHH O X := hKey O (X.m + 1) (x, true) (x, false)

def dgH {X : Loc} (x : X.TT) : X.TT × Bool → ℕ := fun l => dX (x, true) l + dX (x, false) l

def EhatT (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) (P : ℕ) : RHH O X :=
  MvPolynomial.X ((x, true), 0) ^ P * MvPolynomial.X ((x, false), 0) ^ P +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) ^ P * MvPolynomial.X ((x, false), c.succ) ^ P

theorem hTop_eq (x : X.TT) : hTop O X x = MvPolynomial.X ((x, true), 0) * MvPolynomial.X ((x, false), 0) +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) * MvPolynomial.X ((x, false), c.succ) := by
  rw [hTop, hKey, Fin.sum_univ_succ]

theorem EhatT_one (x : X.TT) : EhatT O X x 1 = hTop O X x := by
  rw [EhatT, hTop_eq]
  simp only [pow_one]

private theorem X_true_mul_X_false_pow_mem_Pol (x : X.TT) (a : Fin (X.m + 1)) (P : ℕ) :
    (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P ∈
      Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (fun l => P * dgH x l) := by
  classical
  rw [show (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P =
      monomial (P • (Finsupp.single ((x, true), a) 1 + Finsupp.single ((x, false), a) 1)) 1 by
    rw [MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_pow, one_mul, one_pow]]
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' := support_monomial_subset hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  intro l
  simp only [multideg, dgH, dX, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  congr 1 <;> split_ifs with h <;> simp [h]

theorem hTop_pol (x : X.TT) : hTop O X x ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH x) := by
  have e : hTop O X x = ∑ a : Fin (X.m + 1),
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ 1 := by
    rw [hTop_eq, Fin.sum_univ_succ]
    simp only [pow_one]
  rw [e]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  have h := X_true_mul_X_false_pow_mem_Pol (O := O) x a 1
  simp only [one_mul] at h
  exact h

theorem hTop_nd (x : X.TT) : IsWeightedHomogeneous (wN X) (hTop O X x) 1 := by
  rw [hTop_eq]
  have hpair : ∀ a : Fin (X.m + 1), IsWeightedHomogeneous (wN X)
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) 1 := by
    intro a
    have h1 := (isWeightedHomogeneous_X (KK O) (wN X) ((x, true), a)).mul
      (isWeightedHomogeneous_X (KK O) (wN X) ((x, false), a))
    have hw : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
      rcases Nat.lt_or_ge a.val 1 with h | h
      · have h' : ¬ 1 ≤ a.val := by omega
        simp [wN, h, h']
      · have h' : ¬ a.val < 1 := by omega
        simp [wN, h, h']
    rwa [hw] at h1
  refine (hpair 0).add (IsWeightedHomogeneous.sum _ _ _ (fun c _ => hpair c.succ))

private theorem X_mem_intSub' (v : VarH X) : (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
  classical
  change ∀ m, ∃ a : O, (MvPolynomial.X v : RHH O X).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a)
  intro m
  rw [MvPolynomial.coeff_X']
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem hTop_int (x : X.TT) : hTop O X x ∈ intSub O (VarH X) := by
  rw [hTop_eq]
  exact add_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _))
    (sum_mem fun c _ => mul_mem (X_mem_intSub' _) (X_mem_intSub' _))

theorem hTop_inA (x : X.TT) : InA (hTop O X x) := by
  have h := hTop_int (O := O) x
  change ∀ m, ∃ a : O, (hTop O X x).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a) at h
  intro m
  obtain ⟨a, ha⟩ := h m
  exact ⟨a, by rw [ha, pow_zero, one_mul]⟩

theorem hTop_lift (w : O) (x : X.TT) : lift1 X O w (hTop O X x) = w • hTop O X x := by
  rw [identity_lift_normal_homog w (hTop_nd x), pow_one]

theorem hTop_ord (w : O) (x : X.TT) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (hTop O X x) 1 := by
  exact hook_key_order_ge_one w (hhLetters X.TT) 1 g hg (x, true) (x, false) rfl rfl rfl

theorem softOK_hTop (w : O) (x : X.TT) : SoftOK w (hTop O X x) 1 (hTop O X x) (dgH x) where
  fac := IsFac.of_exact (e := 1) (r := 0) (hTop_inA x) (fun g hg => hTop_ord w x g hg) le_rfl (hTop_inA x)
    ((inA_iff_wj w).2 (wjSub w 0).zero_mem) (by
      have := hTop_lift w x
      rw [smul_zero, add_zero, pow_one]
      exact this)
  sgHom := ndHom_iff.2 (hTop_nd x)
  liftPol := identity_lift_mem_Pol _ (hTop_pol x)
  sgPol := hTop_pol x

theorem EhatT_eq_sum (x : X.TT) (P : ℕ) :
    EhatT O X x P = ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P := by
  rw [EhatT, Fin.sum_univ_succ]
  simp only [mul_pow]

theorem EhatT_int (x : X.TT) (P : ℕ) : EhatT O X x P ∈ intSub O (VarH X) := by
  rw [EhatT_eq_sum]
  exact sum_mem fun a _ => pow_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _)) _

theorem EhatT_wh (wt : VarH X → ℕ) (n : ℕ) (x : X.TT) (P : ℕ) (h : ∀ a, wt ((x, true), a) + wt ((x, false), a) = n) :
    IsWeightedHomogeneous wt (EhatT O X x P) (P * n) := by
  rw [EhatT_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  have h1 := ((isWeightedHomogeneous_X (KK O) wt ((x, true), a)).mul
    (isWeightedHomogeneous_X (KK O) wt ((x, false), a))).pow P
  rwa [h a, smul_eq_mul] at h1

theorem hpow_congr (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    InWj S.w (hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e)) 1 := by
  classical
  set D : MvPolynomial (VarH X) O :=
    (∑ a : Fin (X.m + 1), MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) -
      ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) with hDdef
  have hD : hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e) = MvPolynomial.map (algebraMap O (KK O)) D := by
    rw [EhatT_eq_sum, ← EhatT_one, EhatT_eq_sum, hDdef]
    simp only [map_sub, map_pow, map_sum, map_mul, map_X, pow_one]
  rw [hD]
  apply Formalism.MainNotions.G.WittFrameLocaliserOrders.residue_zero_mem_order_one S
  have hp0 : ((X.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  haveI : CharP (IsLocalRing.ResidueField O) X.p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  rw [hDdef]
  simp only [map_sub, map_pow, map_sum, map_mul, map_X]
  rw [sum_pow_char_pow, sub_self]

theorem softH (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    SoftOK S.w (hTop O X x ^ (X.p ^ e)) (X.p ^ e) (EhatT O X x (X.p ^ e)) (fun l => X.p ^ e * dgH x l) where
  fac := by
    have := ((softOK_hTop S.w x).pow (X.p ^ e)).fac
    rw [mul_one] at this
    exact this.congr_sg (hpow_congr S hS x e) ((mem_intSub O _).1 (EhatT_int x _))
  sgHom := ndHom_iff.2 (by
    have := EhatT_wh (O := O) (wN X) 1 x (X.p ^ e) (wN_pair x)
    rwa [mul_one] at this)
  liftPol := ((softOK_hTop S.w x).pow (X.p ^ e)).liftPol
  sgPol := mem_Pol_iff.2 fun l => EhatT_wh (wL X l) _ x _ fun _ => rfl

theorem softHseg (S : UniformizedDVR X.p O) (hS : S.SqP) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (hTop O X (topOdd X j i) ^ ((X.seg C0 CE1 CE2 j).P X.p i)) ((X.seg C0 CE1 CE2 j).P X.p i)
      (EhatT O X (topOdd X j i) ((X.seg C0 CE1 CE2 j).P X.p i))
      (fun l => (X.seg C0 CE1 CE2 j).P X.p i * dgH (topOdd X j i) l) := by
  exact softH S hS (topOdd X j i) _

theorem sgKS_pow (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (P : ℕ) :
    sgKS O X j i ^ P = MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i * P) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ P := by
  rw [sgKS, mul_pow, ← pow_mul]

end H

end Formalism.MainNotions.ColumnSystems.Pf
