import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
open GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

theorem ratDeg_pull_eq_interNumRed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∀ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ p) 1 → z ≫ w = redι Z ≫ ratFibre.fst p → IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) → ∀ M : LB X, M.IsLB → ratDeg (w ≫ p) (M.pull w) = interNumRed ℚ Z ![M.pull (ratFibre.fst p)] := by
  intro k _ X p Z hZ W w z hW hzw H M hM
  letI iQ : Algebra ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
    algebraΓOfHom (redι Z ≫ ratFibre.snd p)
  have hi : ∀ r : ℚ, (redι Z).appTop (algebraMap ℚ Γ(ratFibre p, ⊤) r) =
      algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun _ ↦ rfl
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  have hC : VB.IsProjCurve ℚ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have hs : strHom ℚ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = redι Z ≫ strHom ℚ (ratFibre p) := by
      rw [ratFibre.strHom_eq]; exact strHom_eq fun _ ↦ rfl
    have hP : IsProper (strHom ℚ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [hs]; exact hZ.isProper
    exact VB.IsProperCurve.isProjCurve ℚ _
      ⟨inferInstance, (topologicalKrullDim_red Z).trans hZ.dim_eq, hP⟩
  set R := ratFibre (w ≫ p)
  set e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ R :=
    H.isoIsPullback _ _ (ratFibre.isPullback (w ≫ p)) with he
  have efst : e.hom ≫ ratFibre.fst (w ≫ p) = z :=
    IsPullback.isoIsPullback_hom_fst _ _ H (ratFibre.isPullback _)
  have hf : ∀ r : ℚ, e.hom.appTop (algebraMap ℚ Γ(R, ⊤) r) =
      algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦
    RingHom.congr_fun (RingHom.ext_rat (e.hom.appTop.hom.comp (algebraMap ℚ _)) (algebraMap ℚ _)) r
  set L := (M.pull w).pull (ratFibre.fst (w ≫ p)) with hLdef
  set N := (M.pull (ratFibre.fst p)).pull (redι Z) with hNdef
  have hL : L.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hN : N.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hLe : (L.pull e.hom).IsLB := Semi.LB.isLB_pull hL _
  have hcls : cls (L.pull e.hom) hLe = cls N hN := by
    rw [cls_pull hL, cls_pull (Semi.LB.isLB_pull hM _), cls_pull hM, cls_pull (Semi.LB.isLB_pull hM _),
      cls_pull hM]
    simp only [← pull_comp, ← Category.assoc, efst, hzw]
  have h₁ : chi ℚ (structureModule R) =
      chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    (chi_congr ℚ (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi ℚ (toMod L) =
      chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) := by
    refine (chi_congr ℚ (Twist.unitTwistIso L)).symm.trans ?_
    refine (chi_congr ℚ ((twistFunctor L).mapIso (asIso (unitToPush e.hom)))).trans ?_
    refine (chi_twist_pushforward_of_isClosedImmersion hf _ L).trans ?_
    exact (nonempty_twist_iso_of_cls_eq _ hLe hN hcls).elim (chi_congr ℚ)
  have h₃ : interNumRed ℚ Z ![M.pull (ratFibre.fst p)] =
      chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) -
        chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    have e₁ := interNumOn_eq_interNum_pull (k := ℚ) (L := ![M.pull (ratFibre.fst p)]) hi
      (fun i ↦ by fin_cases i; exact Semi.LB.isLB_pull hM _)
    have e₂ := hC.degLB_eq_interNum hN
    rw [VB.degLB_eq hN, ← chi_congr ℚ (Twist.unitTwistIso N)] at e₂
    rw [interNumRed_def, interNumSub_def]
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    congr 1
    funext i
    fin_cases i
    rfl
  rw [ratDeg, degOfRank, h₁, h₂, h₃]
  push_cast
  ring

end GlobalTheory.RatFibreClosure
