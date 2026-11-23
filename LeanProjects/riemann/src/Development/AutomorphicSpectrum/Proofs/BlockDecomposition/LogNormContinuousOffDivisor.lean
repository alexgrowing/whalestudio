import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchInt

theorem continuousOn_logNorm_offSupp {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X} (ψ : GlobalTheory.Weight q σ L) (hψ : ψ.IsCInf)
    {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  intro y hy
  obtain ⟨i, hi⟩ := GlobalTheory.CxPts.exists_mem_ptsIn (p := q) (σ := σ) ψ.isLB.cover y
  have hu : GlobalTheory.Cartier.UnitAt (GlobalTheory.Cartier.under y) ((r i : X.functionField)) :=
    GlobalTheory.Cartier.IsRatSec.unitAt ψ.isLB hr hy hi
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hu
  have hgV : genericPoint X ∈ V := GlobalTheory.Cartier.gen_mem hyV
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hV
  have hyV' : y ∈ GlobalTheory.CxPts.ptsIn q σ V := GlobalTheory.CxPts.mem_ptsIn.2 hyV
  have hNo : IsOpen (GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr)) :=
    ((GlobalTheory.CxPts.isOpen_ptsIn V).inter (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
      (GlobalTheory.Cartier.isOpen_offSupp _)
  have hyN : y ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr) := ⟨⟨hyV', hi⟩, hy⟩
  have heq : ∀ z ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr),
      Real.log ‖GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2 =
        GlobalTheory.Cartier.logNorm ψ r z := by
    rintro z ⟨⟨hzV, hzi⟩, hz⟩
    rw [GlobalTheory.Cartier.logNorm_eq ψ hr hz hzi, ← ha hgV, GlobalTheory.Cartier.ratVal_fnOf hzV]
  have hne : GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) y ≠ 0 := by
    rw [← GlobalTheory.Cartier.ratVal_fnOf hyV' hgV, ha hgV]
    exact GlobalTheory.Cartier.ratVal_ne_zero hu
  have hev : ContinuousAt (GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V))) y :=
    (GlobalTheory.CxPts.continuousOn_ev _).continuousAt ((GlobalTheory.CxPts.isOpen_ptsIn V).mem_nhds hyV')
  have hφ : ContinuousAt (ψ.φ i) y := (hψ i y hi).continuousAt
  have hg : ContinuousAt (fun z => Real.log ‖GlobalTheory.CxPts.ev q σ V
      (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2) y :=
    (hev.norm.log (norm_ne_zero_iff.2 hne)).sub (hφ.div_const 2)
  exact (hg.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)).continuousWithinAt

end GlobalTheory.CompanionTheory.MixZ.ArchInt
