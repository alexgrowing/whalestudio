import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.liftCmp_holds :
    UpperTheory.V.KernelIndexFullLattice.LiftCmp := by
  intro E _ _ _ a μ _ μ₁ _ hp v Φ hΦ
  have h1 := Lp.coeFn_compMeasurePreserving (toLp μ₁ v) hp
  have h2 := hp.quasiMeasurePreserving.ae hΦ
  have h3 : ∀ᵐ q ∂(quotMeasure (latticeGL E a) μ),
      (UpperTheory.V.KernelIndexFullLattice.cmp hp v : Quot (latticeGL E a) → ℂ) q = Φ (UpperTheory.V.KernelIndexFullLattice.quotMap E a q) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact hq1.trans hq2
  filter_upwards [ae_quotMeasure_iff.1 h3] with g hg
  rw [← UpperTheory.V.KernelIndexFullLattice.quotMk_holds E a g]
  exact hg
