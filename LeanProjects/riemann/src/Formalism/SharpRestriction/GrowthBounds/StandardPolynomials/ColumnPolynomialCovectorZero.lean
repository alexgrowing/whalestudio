import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RigFactorWeightedHomogeneousLetter

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [local instance] ColSys.fin

section Ctx

variable {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {β : GlobalTheory X} {L : LvDat C0 CE1 CE2 mu X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)}

theorem column_polynomial_covector_zero {w : O} (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) (a : (Cs j).ι)
    (j' : Fin (numSeg X.TT)) : multideg ((Cs j).pl a) (topEnd X j', false) = 0 := by
  classical
  have h : ∀ c, (Cs j).pl a ((topEnd X j', false), c) = 0 := by
    intro c
    have hle : (Cs j).pl a ≤ ∑ b, (Cs j).pl b :=
      Finset.single_le_sum (f := (Cs j).pl) (fun _ _ => zero_le) (Finset.mem_univ a)
    have h2 := hle ((topEnd X j', false), c)
    rw [(Cs j).plSum] at h2
    simp [Finsupp.single_apply] at h2
    exact h2
  simp [multideg, h]

theorem level_degree_le_prime_pow (hp : 0 < X.p) (hGle : ∀ j, segG X.TT j ≤ X.G') (j : Fin (numSeg X.TT))
    (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (l : X.TT × Bool) :
    l2P C0 CE1 CE2 mu X β j i * dgH (l2x C0 CE1 CE2 mu X β j i) l ≤ X.p ^ X.G' := by
  have hd : dgH (l2x C0 CE1 CE2 mu X β j i) l ≤ 1 := by
    rcases l with ⟨y, b⟩
    simp only [dgH, dX, Prod.mk.injEq]
    cases b <;> split_ifs <;> simp_all
  have hP : l2P C0 CE1 CE2 mu X β j i ≤ X.p ^ X.G' := by
    simp only [l2P, SegData.P]
    exact Nat.pow_le_pow_right hp (le_trans (Nat.sub_le _ _) (hGle j))
  calc _ ≤ X.p ^ X.G' * 1 := Nat.mul_le_mul hP hd
    _ = _ := mul_one _

theorem level_degree_covector_zero (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (j' : Fin (numSeg X.TT)) :
    l2P C0 CE1 CE2 mu X β j i * dgH (l2x C0 CE1 CE2 mu X β j i) (topEnd X j', false) = 0 := by
  have hne := topOdd_ne_endAny X j (uTop (X.seg C0 CE1 CE2 j) i) j'
  simp [dgH, dX, l2x, hne]

theorem monomial_mem_support (M : MonH X) : M ∈ (monomial M (1 : KK O) : RHH O X).support := by
  classical
  rw [support_monomial, if_neg one_ne_zero]
  exact Finset.mem_singleton_self _

def lemmaRData (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (hGle : ∀ j, segG X.TT j ≤ X.G')
    (hβ : ∀ j, BLk C0 Cde CE1 CE2 X E j (β j))
    (Cs : ∀ j, ColSys C0 CE1 CE2 X O S.w mu β L j (G j)) (hG0 : ∀ j, G j ≠ 0) (j0 : Fin (numSeg X.TT)) (Std : MonH X)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
    (stdEq : Std = rig L (fun j => (Cs j).a0) j0 +
      ((∑ j, ∑ a, (Cs j).pl a) + ∑ a, multMk X β a • aMk C0 CE1 CE2 X a)) :
    PreSys C0 CE1 CE2 X O S.w mu β L G Std where
  ιC := fun j => (Cs j).ι
  finC := fun j => (Cs j).fin
  Kc := fun j => (Cs j).Kc
  dK := fun j => (Cs j).dK
  pl := fun j => (Cs j).pl
  fC := fun j => (Cs j).fC
  oC := fun j => (Cs j).oC
  dgC := fun j => (Cs j).dgC
  fH := fun j i => hTop O X (l2x C0 CE1 CE2 mu X β j i) ^ l2P C0 CE1 CE2 mu X β j i
  oH := fun j i => l2P C0 CE1 CE2 mu X β j i
  dgH := fun j i l => l2P C0 CE1 CE2 mu X β j i * dgH (l2x C0 CE1 CE2 mu X β j i) l
  ιM := IM X
  finM := inferInstance
  multM := multMk X β
  fM := fMk O C0 CE1 CE2 X
  aM := aMk C0 CE1 CE2 X
  oM := oMk C0 CE1 CE2 X
  dgM := dgMk C0 CE1 CE2 X
  fR := l2sR O L (fun j => (Cs j).a0) j0
  R := rig L (fun j => (Cs j).a0) j0
  oR := ∑ j, L.jp j
  dR := fun l => (∑ j, L.jp j * dgH (topEnd X j) l) + multideg (rig L (fun j => (Cs j).a0) j0) l
  KInt := fun j => (Cs j).KInt
  KPol := fun j => (Cs j).KPol
  digit_le_one := fun j => (Cs j).digit_le_one
  dKsum := fun j => (Cs j).dKsum
  Kprod := fun j => (Cs j).Kprod
  facC := fun j => (Cs j).facC
  homC := fun j => (Cs j).homC
  liftC := fun j a => identity_lift_mem_Pol S.w ((Cs j).fPol a)
  polC := fun j => (Cs j).polC
  plQ := fun j => (Cs j).plQ
  plY := column_polynomial_covector_zero Cs
  facH := fun j i => by rw [lifted_block_generator]; exact (soft_height_bound_segment_power S hS j i).fac
  homH := fun j i => by rw [lifted_block_generator]; exact (soft_height_bound_segment_power S hS j i).sgHom
  liftH := fun j i => (soft_height_bound_segment_power S hS j i).liftPol
  polH := fun j i => by rw [lifted_block_generator]; exact (soft_height_bound_segment_power S hS j i).sgPol
  facM := fun a => (softMk S hS hD h2 C0 CE1 CE2 a).fac
  homM := fun a => (softMk (O := O) S hS hD h2 C0 CE1 CE2 a).sgHom _ (monomial_mem_support _)
  liftM := fun a => (softMk S hS hD h2 C0 CE1 CE2 a).liftPol
  polM := fun a l => ((mem_restrictSupport_iff _).1 (softMk (O := O) S hS hD h2 C0 CE1 CE2 a).sgPol)
    (Finset.mem_coe.2 (monomial_mem_support _)) l
  rigA := algebra_mul_mem (algebra_prod_pow_mem _ _ _ fun j _ => hTop_inA _) (monomial_in_algebra _)
  rigLift := by rw [rigid_factor_product]; exact identity_lift_normal_homog S.w (rig_factor_weighted_homogeneous_total L _ j0)
  rigHom := by rw [rigid_factor_product]; exact ndHom_iff.2 (rig_factor_weighted_homogeneous_total L _ j0)
  rigPol := by rw [rigid_factor_product]; exact mem_Pol_iff.2 (rig_factor_weighted_homogeneous_letter L _ j0)
  rigInt := by
    rw [rigid_factor_product]; exact algebra_mul_mem (algebra_prod_pow_mem _ _ _ fun j _ => hTop_inA _) (monomial_in_algebra _)
  dgCQ := fun j => (Cs j).dgCQ
  dgHQ := level_degree_le_prime_pow (by have := hD.2.1; omega) hGle
  dgMQ := dgMk_le hD hGle C0 CE1 CE2
  dgCY := fun j => (Cs j).dgCY
  dgHY := level_degree_covector_zero
  dgMY := dgMk_Y C0 CE1 CE2
  degEq := multidegree_sum_eq_target_degrees S hS hD h2 hβ Cs hG0 j0 Std hStd stdEq
  stdEq := stdEq
  clean := cleaned_product_order_family_eq S hS hD h2 Cs hG0 j0 Std hStd stdEq
  total := total_product_mem_polynomials S hS hD h2 hβ Cs hG0 j0 Std hStd stdEq
  ordEq := order_sum_eq_order_family S hS hD h2 Cs hG0 j0 Std hStd stdEq

end Ctx

theorem preAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hroom : RoomAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    PreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hS hD hH hc mm _ n hn1 hnc β hβ L G Cs hG0 Std hStd
  have h2 : 2 ≤ numSeg X.TT := hH.1.2.2.2.1
  have hGle : ∀ j, segG X.TT j ≤ X.G' := fun j => (hH.1.2.2.2.2.1 j).1
  have hrm := hroom X hD hH hc n hn1 hnc β hβ (fun j => (Cs j).a0) (fun j => (Cs j).a0le) ⟨0, by omega⟩
  have hsg : ∀ j (i : Fin (segS X.TT j)), ¬ (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (β j).sg i = 0 :=
    fun j i h => ((hβ j).2.1 i (not_lt.1 h)).2.2.2
  have hstd := std_eq O L (fun j => (Cs j).a0) ⟨0, by omega⟩ hsg hrm Std hStd
  have hplsum : ∑ j, ∑ a, (Cs j).pl a = ∑ j, (Finsupp.single ((topStart X j, true), 0)
      ((X.seg C0 CE1 CE2 j).Qj X.p * (Cs j).a0) + zPart C0 CE1 CE2 X β j) :=
    Finset.sum_congr rfl fun j _ => (Cs j).plSum
  refine ⟨lemmaRData S hS hD h2 hGle hβ Cs hG0 ⟨0, by omega⟩ Std hStd ?_⟩
  rw [hplsum, sum_aMk]
  exact hstd

theorem restPre : RestPre := TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => preAt_of h) restRoom

end Formalism.MainNotions.ColumnSystems.Pf
