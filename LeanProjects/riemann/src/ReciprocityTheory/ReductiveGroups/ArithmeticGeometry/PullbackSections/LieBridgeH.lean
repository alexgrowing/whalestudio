import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

abbrev IxB (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def eB (Dw : Datum H) : Fin (Fintype.card (IxB Dw)) ≃ IxB Dw := (Fintype.equivFin (IxB Dw)).symm

theorem hS (x : Sp S ⟶ Xo.X) :
    IsGrpPullback ((Over.pullback x).obj Xo.univ.t.G) Xo.univ.t.G x (pullback.fst Xo.univ.t.G.hom x) :=
  isGrpPullback_pullback Xo.univ.t.G x

def uS (y : FrPt Xo c S) (i : Fin (Fintype.card (IxB Dw))) : epsR S ⟶ (Over.pullback y.x).obj Xo.univ.t.G :=
  (push_surj (hS y.x) (tv (fullB y (eB Dw i)))).choose

theorem push_uS (y : FrPt Xo c S) (i : Fin (Fintype.card (IxB Dw))) :
    pushHom (hS y.x) (epsR S) (uS y i) = tv (fullB y (eB Dw i)) :=
  (push_surj (hS y.x) (tv (fullB y (eB Dw i)))).choose_spec

theorem uS_basis (y : FrPt Xo c S) : IsLieBasis (uS y) := by
  refine ⟨fun i => (isTangent_iff (hS y.x) _).2 (by rw [push_uS]; exact tv_mem _), fun w hw => ?_⟩
  have hw' := (isTangent_iff (hS y.x) w).1 hw
  let m : TanM y.x Xo.univ.t.G := mkT _ hw'
  have key : ∀ a : Fin (Fintype.card (IxB Dw)) → S,
      IsLieComb a (uS y) w ↔ m = ∑ k, (a ((eB Dw).symm k)) • fullB y k := by
    intro a
    rw [isLieComb_iff (hS y.x)]
    constructor
    · intro h
      apply tanM_ext
      rw [tv_mkT, h, tv_sum, ← (eB Dw).prod_comp]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply, tv_smul]
      exact congrArg _ (push_uS y i)
    · intro h
      have := congrArg tv h
      rw [tv_mkT, tv_sum, ← (eB Dw).prod_comp] at this
      rw [this]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply, tv_smul]
      exact congrArg _ (push_uS y i).symm
  obtain ⟨A, hA, hAu⟩ := fullB_basis y m
  refine ⟨fun i => A (eB Dw i), (key _).2 (by simpa using hA), fun b hb => ?_⟩
  have := hAu (fun k => b ((eB Dw).symm k)) ((key b).1 hb)
  funext i
  simpa using congrFun this (eB Dw i)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
