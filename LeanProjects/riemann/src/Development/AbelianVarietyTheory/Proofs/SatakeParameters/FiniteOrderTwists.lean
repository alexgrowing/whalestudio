import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TaylorYoshidaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

end GlobalTheory.RoadU.FinTwist

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

theorem isAlg_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {κ : HChar K} {m : ℕ} (hm : 0 < m)
    (h : κ ^ m = 1) : κ.IsAlg 0 := fun k => isAlgPos_zero_of_orderDvd hm h k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem infChar_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (P : CuspSub K n) {κ : HChar K}
    (hκ : κ.IsAlg 0) (τ : K →+* ℂ) : (CG.mk (P.twist κ)).infChar τ = (CG.mk P).infChar τ := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 0 hκ τ]
  simp

end GlobalTheory.RoadU.FinTwist
