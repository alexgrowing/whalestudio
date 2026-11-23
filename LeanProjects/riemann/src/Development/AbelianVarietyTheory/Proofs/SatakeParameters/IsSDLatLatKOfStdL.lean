import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatAndDlEqOfIsSDLatMvL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KerSelfDual

theorem isSDLat_latK_of_stdL : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (co : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → latCo D.sp (gramN D i hi) co a 1 lev.Lb = StandardLatticesGL3.stdL D (D.R.N i) → ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsSDLat D.host.E (D.R.N i) (latK D.sp (gramN D i hi) a x.1 lev.Lb) := by
  intro D i hi T bad lev co a hco hstd x
  have hc : IsOrthCo ((sigD D : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) :=
    GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ co hco
  have hc' : ∃ c, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) c := ⟨toLE co, hc⟩
  have hJ := GlobalTheory.isLat_dl_of_isOrthCo D.sp (gramN D i hi) hc'
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have h1 : Formalism.L2.PairingIndexBounds.F.latAd (1 : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) lev.Lb = lev.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one hLb
  have hm : mvL co (compan (sp := D.sp) (gramN D i hi) a lev.Lb) = StandardLatticesGL3.stdL D (D.R.N i) := by
    rw [← hstd, latCo, h1]
  have hsd := GlobalTheory.FourthRootStd.stdL_isSD D (D.R.N i)
  rw [← hm] at hsd
  obtain ⟨hM, hdl⟩ := GlobalTheory.OrthSelfDual.isLat_and_dl_eq_of_isSDLat_mvL D.sp (gramN D i hi) co _ hc hsd
  exact GlobalTheory.SDCompan.isSDLat_latK D.sp (gramN D i hi) hJ hc' x.1 x.2 lev.Lb a hLb hM hdl

end GlobalTheory.KerSelfDual
