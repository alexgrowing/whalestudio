import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitPt

theorem isUnit_gs_of_mem_basicOpen {X Y : Scheme.{0}} (T : X ⟶ Y) (x : X) (U : Y.Opens) (h : T x ∈ U) (a : Γ(Y, U))
    (ha : T x ∈ Y.basicOpen a) : IsUnit (gs T x U a) := by
  rw [gs_eq T x U h]
  have hu := (Y.mem_basicOpen a (T x) h).1 ha
  rw [← Scheme.Hom.germ_stalkMap_apply T U x h a]
  exact hu.map _

theorem exists_unit_sval (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (α ν : Q.X)
    (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k))) (hs : ¬ ∀ j, s.f j = 0) :
    ∃ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J ∧ IsUnit (sval s (DegPre.trF Q (FractionRing R) ν).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hs
  have hsm := Q.P.isAb.smooth
  let p : (DegPre.BF Q (FractionRing R)).left ⟶ Spec (CommRingCat.of (FractionRing R)) :=
    (fst (TF (R := R) (FractionRing R)) Q.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) (FractionRing R)).hom Q.P.A.hom))
  have : IsReduced (DegPre.BF Q (FractionRing R)).left := isReduced_of_smooth p
  have hne : (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) ≠ ⊥ := fun h =>
    hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) := by
    by_contra h
    push_neg at h
    exact hne (eq_bot_iff.2 fun x hx => (h x hx).elim)
  have hwU := Scheme.basicOpen_le _ _ hw
  set T := (DegPre.trF Q (FractionRing R) ν).left with hT
  let z := (DegPre.trF Q (FractionRing R) (-ν)).left w
  have hz : T z = w := by
    change ((DegPre.trF Q (FractionRing R) (-ν)).left ≫ T) w = w
    rw [hT, ← Over.comp_left, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_add, neg_add_cancel, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_zero]
    rfl
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.P.L z J := ⟨_, fun ψ => (exists_chart Q.P.isLB (ψ z)).choose_spec⟩
  refine ⟨z, J, hJ, ?_⟩
  have hz' : T z ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) α) j := hz ▸ hwU
  have hzb : T z ∈ (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) := hz ▸ hw
  rw [sval, sec_trans s T z (hJ.mem _ T) hz']
  exact (Units.isUnit _).mul (isUnit_gs_of_mem_basicOpen T z _ hz' (s.f j) hzb)

end GlobalTheory.UnitPt
