import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialLogGrowthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelChartFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPolydiscExistsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormAtContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialFormPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormTwoSidedBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorBoundaryPotentialsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalConjOfNotGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalOfGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSncPullbackSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormCompactBounds
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdGram

section Pure

open Matrix Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms GlobalTheory.HermFrame GlobalTheory.CurvInterp GlobalTheory.MatDeriv
open scoped ComplexOrder

end Pure

section Obj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CurvInterp in

theorem hodgeLocal_all {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) : HodgeLocal x σ := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good D A N j S κ s x σ h
  · refine GlobalTheory.CurvInterp.HodgeConj.hodgeLocal_of_conj D A N j S κ s x σ h
      (GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good D A N j S κ s x _ ?_)
    have h' : ¬ GoodEmb κ.c σ := h
    have h1 : GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by simpa only [goodOf, if_neg h'] using goodEmb_goodOf κ.c σ
    exact h1

end Obj

end GlobalTheory.BdGram
