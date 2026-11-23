import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColumnWordMemPolynomialsOfDegree

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [local instance] ColSys.fin

section Ctx

variable {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {β : GlobalTheory X} {L : LvDat C0 CE1 CE2 mu X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)}

theorem soft_height_bound_segment_power (S : UniformizedDVR X.p O) (hS : S.SqP) (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    SoftOK S.w (hTop O X (l2x C0 CE1 CE2 mu X β j i) ^ l2P C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i)
      (EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i))
      (fun l => l2P C0 CE1 CE2 mu X β j i * dgH (l2x C0 CE1 CE2 mu X β j i) l) :=
  softHseg S hS C0 CE1 CE2 j _

theorem rig_factor_weighted_homogeneous_total (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) :
    IsWeightedHomogeneous (wN X) (l2sR O L a0 j0) (∑ j, L.jp j) := by
  refine wh_congr (rigid_product_weighted_homog L a0 j0 (wN X) (fun _ => 1) fun x => hTop_nd x) ?_
  rw [← ndM_eq, nd_rig]
  simp

theorem rig_factor_weighted_homogeneous_letter (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) (l : X.TT × Bool) :
    IsWeightedHomogeneous (wL X l) (l2sR O L a0 j0)
      ((∑ j, L.jp j * dgH (topEnd X j) l) + multideg (rig L a0 j0) l) := by
  refine wh_congr (rigid_product_weighted_homog L a0 j0 (wL X l) (fun x => dgH x l) fun x => mem_Pol_iff.1 (hTop_pol x) l) ?_
  rw [← multideg_eq]

variable (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT)
  (hβ : ∀ j, BLk C0 Cde CE1 CE2 X E j (β j))
  (Cs : ∀ j, ColSys C0 CE1 CE2 X O S.w mu β L j (G j)) (hG0 : ∀ j, G j ≠ 0) (j0 : Fin (numSeg X.TT)) (Std : MonH X)
  (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
  (stdEq : Std = rig L (fun j => (Cs j).a0) j0 +
      ((∑ j, ∑ a, (Cs j).pl a) + ∑ a, multMk X β a • aMk C0 CE1 CE2 X a))

include hS hD h2 hG0 hStd stdEq in
theorem order_sum_eq_order_family : (∑ j, L.jp j) + ((∑ j, ∑ a, (Cs j).oC a) + ((∑ j, ∑ i, L.lv j i * l2P C0 CE1 CE2 mu X β j i) +
      ∑ a, multMk X β a * oMk C0 CE1 CE2 X a)) = ordFam C0 CE1 CE2 X β := by
  have hp : 0 < X.p := by have := hD.2.1; omega
  have h := wh_total (wN X) (rig_factor_weighted_homogeneous_total (O := O) L (fun j => (Cs j).a0) j0)
    (sC := fun j a => l2sC Cs j a) (dC := fun j a => (Cs j).oC a)
    (fun j a => ndHom_iff.1 (fun m hm => (Cs j).homC a m hm))
    (fun j i => ndHom_iff.1 (soft_height_bound_segment_power (C0 := C0) (CE1 := CE1) (CE2 := CE2) (mu := mu) (β := β) S hS j i).sgHom)
    (fun a => ndHom_iff.1 (softMk (O := O) S hS hD h2 C0 CE1 CE2 a).sgHom) L.lv (multMk X β)
  rw [sym_family_eq_sigma_product Cs j0 Std hStd stdEq] at h
  exact IsWeightedHomogeneous.inj_right (sym_family_word_ne_zero hp L G hG0 Std hStd) h (symNdBL β _ (balanced_word_homogeneous L G (column_word_mem_polynomials_of_degree Cs)))

include hS hD h2 hβ hG0 hStd stdEq in
theorem multidegree_sum_eq_target_degrees (l : X.TT × Bool) : ((∑ j, L.jp j * dgH (topEnd X j) l) + multideg (rig L (fun j => (Cs j).a0) j0) l) +
      ((∑ j, ∑ a, (Cs j).dgC a l) + ((∑ j, ∑ i, L.lv j i * (l2P C0 CE1 CE2 mu X β j i * dgH (l2x C0 CE1 CE2 mu X β j i) l)) +
      ∑ a, multMk X β a * dgMk C0 CE1 CE2 X a l)) = hhDegs X.TT X.aT X.bT l := by
  have hp : 0 < X.p := by have := hD.2.1; omega
  have h := wh_total (wL X l) (rig_factor_weighted_homogeneous_letter (O := O) L (fun j => (Cs j).a0) j0 l)
    (sC := fun j a => l2sC Cs j a) (dC := fun j a => (Cs j).dgC a l)
    (fun j a => mem_Pol_iff.1 ((Cs j).polC a) l)
    (fun j i => mem_Pol_iff.1 (soft_height_bound_segment_power (C0 := C0) (CE1 := CE1) (CE2 := CE2) (mu := mu) (β := β) S hS j i).sgPol l)
    (fun a => mem_Pol_iff.1 (softMk (O := O) S hS hD h2 C0 CE1 CE2 a).sgPol l) L.lv (multMk X β)
  rw [sym_family_eq_sigma_product Cs j0 Std hStd stdEq] at h
  exact IsWeightedHomogeneous.inj_right (sym_family_word_ne_zero hp L G hG0 Std hStd) h
    (mem_Pol_iff.1 (symPolBL h2 β hβ _ (balanced_word_homogeneous L G (column_word_mem_polynomials_of_degree Cs))) l)

include hS hD h2 hβ hG0 hStd stdEq in
theorem total_product_mem_polynomials : l2sR O L (fun j => (Cs j).a0) j0 * ((∏ j, ∏ a, (Cs j).fC a) *
      ((∏ j, ∏ i, (hTop O X (l2x C0 CE1 CE2 mu X β j i) ^ l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
        ∏ a, fMk O C0 CE1 CE2 X a ^ multMk X β a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) := by
  refine mem_Pol_iff.2 fun l => wh_congr (wh_total (wL X l) (rig_factor_weighted_homogeneous_letter (O := O) L (fun j => (Cs j).a0) j0 l)
    (sC := fun j a => (Cs j).fC a) (dC := fun j a => (Cs j).dgC a l)
    (fun j a => mem_Pol_iff.1 ((Cs j).fPol a) l)
    (dH := fun j i => l2P C0 CE1 CE2 mu X β j i * dgH (l2x C0 CE1 CE2 mu X β j i) l)
    (fun j i => ?_) (fun a => mem_Pol_iff.1 (fMk_pol C0 CE1 CE2 a) l) L.lv (multMk X β))
    (multidegree_sum_eq_target_degrees S hS hD h2 hβ Cs hG0 j0 Std hStd stdEq l)
  have := (mem_Pol_iff.1 (hTop_pol (O := O) (l2x C0 CE1 CE2 mu X β j i)) l).pow (l2P C0 CE1 CE2 mu X β j i)
  rwa [smul_eq_mul] at this

include hS hD h2 hG0 hStd stdEq in
theorem cleaned_product_order_family_eq (g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg' : IsGLW g')
    (hne : ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 1) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g'
      (l2sR O L (fun j => (Cs j).a0) j0 * ((∏ j, ∏ a, (Cs j).fC a) *
      ((∏ j, ∏ i, (hTop O X (l2x C0 CE1 CE2 mu X β j i) ^ l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
        ∏ a, fMk O C0 CE1 CE2 X a ^ multMk X β a))) (ordFam C0 CE1 CE2 X β + X.c) := by
  have hrig : (monomial (rig L (fun j => (Cs j).a0) j0) (1 : KK O) : RHH O X) =
      monomial (rig0 L (fun j => (Cs j).a0) j0) 1 * MvPolynomial.X ((topStart X j0, true), 0) ^ X.c := by
    unfold rig
    rw [X_pow_eq_monomial, monomial_mul, one_mul]
  have hloc : locR O X j0 ^ X.c = MvPolynomial.X ((topStart X j0, true), 0) ^ X.c * ∏ c : Fin X.m, locC O X c.succ ^ X.c := by
    unfold locR
    rw [mul_pow, Finset.prod_pow]
  have hF : l2sR O L (fun j => (Cs j).a0) j0 * ((∏ j, ∏ a, (Cs j).fC a) *
      ((∏ j, ∏ i, (hTop O X (l2x C0 CE1 CE2 mu X β j i) ^ l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
        ∏ a, fMk O C0 CE1 CE2 X a ^ multMk X β a)) =
      locR O X j0 ^ X.c * (((∏ j, hTop O X (topEnd X j) ^ L.jp j) * monomial (rig0 L (fun j => (Cs j).a0) j0) 1) *
        ((∏ j, ∏ a, (Cs j).fC a) *
        ((∏ j, ∏ i, (hTop O X (l2x C0 CE1 CE2 mu X β j i) ^ l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
      ∏ a, fMk O C0 CE1 CE2 X a ^ multMk0 X β a))) := by
    rw [product_split_constant, hloc]
    unfold l2sR
    rw [hrig]
    ring
  rw [hF]
  have hR0 : InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g'
      ((∏ j, hTop O X (topEnd X j) ^ L.jp j) * monomial (rig0 L (fun j => (Cs j).a0) j0) 1) ((∑ j, L.jp j * 1) + 0) :=
    inWjRg_mul (inWjRg_prod _ _ _ fun j _ => inWjRg_pow (hTop_ord S.w _ g' hg') _)
      (inWjRg_zero_of_inA S.w (monomial_in_algebra _) g' hg')
  have h := inWjRg_mul (locPow_ord S hS hD h2 j0 g' hg' hne X.c)
    (order_total_bound hR0 (sC := fun j a => (Cs j).fC a) (dC := fun j a => (Cs j).oC a)
      (fun j a => ((Cs j).facC a).ord g' hg')
      (fun j i => (soft_height_bound_segment_power (C0 := C0) (CE1 := CE1) (CE2 := CE2) (mu := mu) (β := β) S hS j i).fac.ord g' hg')
      (fun a => (softMk (O := O) S hS hD h2 C0 CE1 CE2 a).fac.ord g' hg') L.lv (multMk0 X β))
  have e : X.c + (((∑ j, L.jp j * 1) + 0) + ((∑ j, ∑ a, (Cs j).oC a) + ((∑ j, ∑ i, L.lv j i * l2P C0 CE1 CE2 mu X β j i) +
      ∑ a, multMk0 X β a * oMk C0 CE1 CE2 X a))) = ordFam C0 CE1 CE2 X β + X.c := by
    rw [sum_split_constant, ← order_sum_eq_order_family S hS hD h2 Cs hG0 j0 Std hStd stdEq]
    simp only [mul_one, add_zero]
    ring
  rw [e] at h
  exact h

end Ctx

end Formalism.MainNotions.ColumnSystems.Pf
