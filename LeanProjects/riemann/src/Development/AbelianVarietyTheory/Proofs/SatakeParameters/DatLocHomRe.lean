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

namespace GlobalTheory.TwU

theorem datLoc_homRe : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (M : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin b' → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a' b' → ℂ), HEq N M → HEq N' M' → DatLoc D cc SS cl M M' Ξ → DatLoc D cc SS cl N N' (fun z => Ξ (homRe ha hb z)) := by
  intro D cc SS cl a b a' b' ha hb N N' M M' Ξ hN hN' h
  subst ha hb
  cases eq_of_heq hN
  cases eq_of_heq hN'
  have hx : (fun z => Ξ (homRe rfl rfl z)) = Ξ := by
    funext z
    congr 1
  rw [hx]
  exact h

end GlobalTheory.TwU
