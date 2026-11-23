import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterNumRedCloPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurfDeg

theorem cxDeg_pullback_eq_topSelf : ∀ (k : Type) [CommRing k] (X S : Scheme.{0}) (p : X ⟶ Sp k) (i : S ⟶ X), IsArithVar (i ≫ p) 1 → ∀ (E : X.Modules) (r : ℕ), VB.IsVB E r → cxDeg (i ≫ p) ((Scheme.Modules.pullback i).obj E) r = topSelfIntersection ℂ (((VB.det E r).pull i).pull (cxFibre.fst (i ≫ p))) 1 := by
  intro k _ X S p i hS E r hE
  have cS := GlobalTheory.T.rational_fibre_projective_curve k S (i ≫ p) hS
  have := cS.isIntegral
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hS.finite
  have : IsProper (i ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hS.isProjOver).1
  have hE' := hE.pullback i
  have hA := Semi.LB.isLB_pull hE.isLB_det i
  have c : CechPic.cls _ hA = CechPic.cls _ hE'.isLB_det :=
    (CechPic.cls_eq_iff hA hE'.isLB_det).2 (hE.lbIso_det_pullback i)
  have hA' := Semi.LB.isLB_pull hA (ratFibre.fst (i ≫ p))
  have hB' := Semi.LB.isLB_pull hE'.isLB_det (ratFibre.fst (i ≫ p))
  rw [ChernDegree.cxDeg_eq_ratDeg hS hE', DegRec.topSelf_cxFibre (i ≫ p) hA,
    ratDeg_eq_degLB hE'.isLB_det, cS.degLB_eq_interNum hB']
  refine interNum_congr_cls _ _ (fun j => by fin_cases j; exact hB') (fun _ => hA') fun j => ?_
  fin_cases j
  refine (CechPic.cls_pull hE'.isLB_det _ _).trans (Eq.trans ?_ (CechPic.cls_pull hA _ _).symm)
  rw [c]

end GlobalTheory.SurfDeg
