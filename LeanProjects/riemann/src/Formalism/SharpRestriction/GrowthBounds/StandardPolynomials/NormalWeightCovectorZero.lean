import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IdentityLiftWeightedHomog

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section Wts

variable {X : Loc}

theorem normal_weight_vector_zero_eq_zero (x : X.TT) : wN X ((x, true), 0) = 0 := by
  simp [wN]
theorem wN_vecS (x : X.TT) (c : Fin X.m) : wN X ((x, true), c.succ) = 1 := by
  simp [wN, Fin.val_succ]
theorem normal_weight_covector_zero (x : X.TT) : wN X ((x, false), 0) = 1 := by
  simp [wN]
theorem wN_covS (x : X.TT) (c : Fin X.m) : wN X ((x, false), c.succ) = 0 := by
  simp [wN, Fin.val_succ]

theorem wN_pair (x : X.TT) (a : Fin (X.m + 1)) : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
  unfold wN
  split_ifs <;> simp_all <;> omega

variable {K : Type} [CommRing K] {σ : Type}

theorem wh_powX (wt : σ → ℕ) (v1 v2 : σ) (a : ℕ) :
    IsWeightedHomogeneous wt ((MvPolynomial.X v1 : MvPolynomial σ K) ^ a * MvPolynomial.X v2) (a * wt v1 + wt v2) := by
  exact ((isWeightedHomogeneous_X K wt v1).pow a).mul (isWeightedHomogeneous_X K wt v2)

theorem wh_Xpow (wt : σ → ℕ) (v1 v2 : σ) (a : ℕ) :
    IsWeightedHomogeneous wt ((MvPolynomial.X v1 : MvPolynomial σ K) * MvPolynomial.X v2 ^ a) (wt v1 + a * wt v2) := by
  exact (isWeightedHomogeneous_X K wt v1).mul ((isWeightedHomogeneous_X K wt v2).pow a)

theorem wh_sub {wt : σ → ℕ} {n : ℕ} {P Q : MvPolynomial σ K} (hP : IsWeightedHomogeneous wt P n)
    (hQ : IsWeightedHomogeneous wt Q n) : IsWeightedHomogeneous wt (P - Q) n := by
  intro d hd
  rw [coeff_sub] at hd
  by_cases h : coeff d P = 0
  · rw [h, zero_sub, neg_ne_zero] at hd
    exact hQ hd
  · exact hP h

end Wts

section Soft

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem SoftOK.pow {w : O} {f sg : RHH O X} {od : ℕ} {dg : X.TT × Bool → ℕ} (h : SoftOK w f od sg dg) (u : ℕ) :
    SoftOK w (f ^ u) (u * od) (sg ^ u) (fun l => u * dg l) where
  fac := h.fac.pow u
  sgHom := ndHom_iff.2 (by simpa [smul_eq_mul] using (ndHom_iff.1 h.sgHom).pow u)
  liftPol := mem_Pol_iff.2 fun l => by
    rw [map_pow]
    simpa [smul_eq_mul] using (mem_Pol_iff.1 h.liftPol l).pow u
  sgPol := mem_Pol_iff.2 fun l => by simpa [smul_eq_mul] using (mem_Pol_iff.1 h.sgPol l).pow u

def sgKS (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0)

def dgKS (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT × Bool → ℕ := fun l =>
  X.p ^ (segDists X.TT j).get i * dX (topStart X j, true) l + dX (topOdd X j i, false) l

theorem two_le_pd (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    1 ≤ X.p ^ (segDists X.TT j).get i - 1 := by
  have hp5 : 5 ≤ X.p := hD.2.1
  have key : ∀ d ∈ segDists X.TT j, 0 < d := by
    intro d hd
    unfold segDists at hd
    simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    exact hs.2.2.1
  have hpos := key _ (List.get_mem _ i)
  have : X.p ≤ X.p ^ (segDists X.TT j).get i := Nat.le_self_pow hpos.ne' X.p
  omega

theorem kS_pol (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    kSkey O X j i ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgKS X j i) := by
  rw [mem_Pol_iff]
  intro l
  unfold kSkey
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  exact wh_powX (K := KK O) (wL X l) ((topStart X j, true), a) ((topOdd X j i, false), a)
    (X.p ^ (segDists X.TT j).get i)

theorem kS_inA (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : InA (kSkey O X j i) := by
  intro m
  refine ⟨(∑ a : Fin (X.m + 1), (MvPolynomial.X ((topStart X j, true), a) : MvPolynomial (VarH X) O) ^
    (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [kSkey, map_sum, map_mul, map_pow, map_X]

theorem softKS (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (kSkey O X j i) 1 (sgKS O X j i) (dgKS X j i) where
  fac := by
    refine IsFac.of_exact (e := X.p ^ (segDists X.TT j).get i - 1)
      (r := ∑ c : Fin X.m, MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
        MvPolynomial.X ((topOdd X j i, false), c.succ)) (kS_inA j i)
      (fun g hg => (key3Ord X O S hS hD j i g hg).1) (two_le_pd hD j i) ?_ ?_ ?_
    · exact (mem_intSub O _).1 (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_int _) _) (X_int _))
    · exact (mem_intSub O _).1 (Subalgebra.sum_mem _ fun a _ =>
        Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_int _) _) (X_int _))
    · rw [key3One_S, pow_one]; rfl
  sgHom := ndHom_iff.2 (by
    have := wh_powX (K := KK O) (wN X) ((topStart X j, true), 0) ((topOdd X j i, false), 0)
      (X.p ^ (segDists X.TT j).get i)
    rwa [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, mul_zero, zero_add] at this)
  liftPol := identity_lift_mem_Pol _ (kS_pol j i)
  sgPol := mem_Pol_iff.2 fun l => wh_powX (wL X l) _ _ _

theorem softKSP (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (P : ℕ) : SoftOK S.w (kSkey O X j i ^ P) P (sgKS O X j i ^ P) (fun l => P * dgKS X j i l) := by
  have h := (softKS S hS hD j i).pow P
  rwa [mul_one] at h

def sgKW (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i)

def dgKW (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT × Bool → ℕ := fun l =>
  dX (topOdd X j i, true) l + X.p ^ (segDists X.TT j).get i * dX (topStart X j, true) l

theorem kW_pol (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin (X.m + 1)) :
    kWkey O X j i c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgKW X j i) := by
  rw [mem_Pol_iff]
  intro l
  unfold kWkey
  exact wh_sub (wh_Xpow (K := KK O) (wL X l) _ _ _) (wh_Xpow (K := KK O) (wL X l) _ _ _)

theorem kW_inA (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin (X.m + 1)) : InA (kWkey O X j i c) := by
  intro m
  refine ⟨((MvPolynomial.X ((topOdd X j i, true), c) : MvPolynomial (VarH X) O) *
      MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) *
      MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [kWkey, map_sub, map_mul, map_pow, map_X]

theorem softKW (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin X.m) : SoftOK S.w (kWkey O X j i c.succ) 1 (sgKW O X j i c) (dgKW X j i) where
  fac := by
    refine IsFac.of_exact (e := X.p ^ (segDists X.TT j).get i - 1)
      (r := -(MvPolynomial.X ((topOdd X j i, true), 0) *
        MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i))) (kW_inA j i _)
      (fun g hg => (key3Ord X O S hS hD j i g hg).2 c) (two_le_pd hD j i) ?_ ?_ ?_
    · exact (mem_intSub O _).1 (Subalgebra.mul_mem _ (X_int _) (Subalgebra.pow_mem _ (X_int _) _))
    · exact (mem_intSub O _).1 (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (X_int _) (Subalgebra.pow_mem _ (X_int _) _)))
    · rw [key_lift_identity_lower, pow_one, smul_neg, ← sub_eq_add_neg]; rfl
  sgHom := ndHom_iff.2 (by
    have := wh_Xpow (K := KK O) (wN X) ((topOdd X j i, true), c.succ) ((topStart X j, true), 0)
      (X.p ^ (segDists X.TT j).get i)
    rwa [normal_weight_vector_zero_eq_zero, wN_vecS, mul_zero, add_zero] at this)
  liftPol := identity_lift_mem_Pol _ (kW_pol j i _)
  sgPol := mem_Pol_iff.2 fun l => wh_Xpow (wL X l) _ _ _

def sgLoc (O : Type) [CommRing O] [IsDomain O] (X : Loc) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1)

def dgLoc (X : Loc) : X.TT × Bool → ℕ := fun l =>
  ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) * dX (topStart X j, true) l

theorem wh_prodStart (wt : VarH X → ℕ) (c : Fin (X.m + 1)) :
    IsWeightedHomogeneous wt
      (∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : RHH O X) ^ (X.p ^ segG X.TT j - 1))
      (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) * wt ((topStart X j, true), c)) := by
  refine IsWeightedHomogeneous.prod _ _ _ (fun j _ => ?_)
  exact (isWeightedHomogeneous_X (KK O) wt ((topStart X j, true), c)).pow _

theorem loc_pol (c : Fin (X.m + 1)) : locC O X c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgLoc X) := by
  rw [mem_Pol_iff]
  intro l
  unfold locC
  exact wh_sub (wh_prodStart (O := O) (wL X l) 0) (wh_prodStart (O := O) (wL X l) c)

theorem prodStart_int (c : Fin (X.m + 1)) :
    (∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : RHH O X) ^ (X.p ^ segG X.TT j - 1)) ∈
      intSub O (VarH X) := by
  have hX : ∀ v : VarH X, (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
    intro v m
    refine ⟨if Finsupp.single v 1 = m then 1 else 0, ?_⟩
    rw [coeff_X']
    split_ifs <;> simp
  exact Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (hX _) _

theorem loc_inA (c : Fin (X.m + 1)) : InA (locC O X c) := by
  intro m
  refine ⟨((∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), 0) : MvPolynomial (VarH X) O) ^
      (X.p ^ segG X.TT j - 1)) -
    ∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : MvPolynomial (VarH X) O) ^
      (X.p ^ segG X.TT j - 1)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [locC, map_sub, map_prod, map_pow, map_X]

theorem one_le_Mp (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) : 1 ≤ ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) := by
  have hn' : 2 ≤ X.n' := hD.2.2.1
  have hp5 : 5 ≤ X.p := hD.2.1
  have hj : ∀ j, 1 ≤ X.p ^ segG X.TT j - 1 := by
    intro j
    have hg : 1 ≤ segG X.TT j := by
      unfold segG
      split_ifs with h
      · omega
      · omega
    have : X.p ≤ X.p ^ segG X.TT j := Nat.le_self_pow (by omega) X.p
    omega
  have j0 : Fin (numSeg X.TT) := ⟨0, by omega⟩
  calc 1 ≤ X.p ^ segG X.TT j0 - 1 := hj j0
    _ ≤ ∑ j, (X.p ^ segG X.TT j - 1) :=
      Finset.single_le_sum (f := fun j => X.p ^ segG X.TT j - 1) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j0)

theorem softLoc (w : O) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (c : Fin X.m) :
    SoftOK w (locC O X c.succ) 0 (sgLoc O X) (dgLoc X) where
  fac := by
    refine IsFac.of_exact (e := ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1))
      (r := -(∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1)))
      (loc_inA _) (fun g hg => inWjRg_zero_of_inA w (loc_inA _) g hg) (one_le_Mp hD h2) ?_ ?_ ?_
    · exact (mem_intSub O _).1 (prodStart_int 0)
    · exact (mem_intSub O _).1 (Subalgebra.neg_mem _ (prodStart_int _))
    · rw [loc4One, pow_zero, one_smul, smul_neg, ← sub_eq_add_neg]; rfl
  sgHom := ndHom_iff.2 (by
    have := wh_prodStart (O := O) (wN X) 0
    simp only [normal_weight_vector_zero_eq_zero, mul_zero, Finset.sum_const_zero] at this
    exact this)
  liftPol := identity_lift_mem_Pol _ (loc_pol _)
  sgPol := mem_Pol_iff.2 fun l => wh_prodStart (wL X l) 0

theorem locPow_ord (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (j0 : Fin (numSeg X.TT))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g)
    (hne : ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1) (n : ℕ) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0 ^ n) n := by
  have := inWjRg_pow (loc4Ord_of (loc4Div_of loc4Res) X O S hS hD h2 j0 g hg hne) n
  rwa [mul_one] at this

end Soft

end Formalism.MainNotions.ColumnSystems.Pf
