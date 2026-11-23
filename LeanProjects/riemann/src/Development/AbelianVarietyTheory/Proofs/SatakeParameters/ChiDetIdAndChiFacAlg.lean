import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAllOfJetMomR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SelfDualChiAlg

theorem chi_detId_and_chiFac_alg : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
    (∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L →
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∈ TaylorLogMetric.Qbar) ∧
    ∀ {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      TaylorLogMetric.admitted D N N' L L' → Base.chiFac χ N N' L L' ∈ TaylorLogMetric.Qbar ∧ Base.chiFac χ N N' L L' ≠ 0 := by
  intro D χ hχ
  refine ⟨fun N L hN hL => ?_, fun L L' hA => ⟨GlobalTheory.MomT.FromComb.chiFac_mem hχ hA, ?_⟩⟩
  · exact GlobalTheory.MomT.FromComb.chi_mem hχ
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ L hN (GlobalTheory.FourthRootStd.stdL_isSD D N) hL)
  · exact GlobalTheory.Mem.NatEqui.chiFac_ne_zero hχ hA.2.2.1 hA.2.2.2

end GlobalTheory.SelfDualChiAlg
