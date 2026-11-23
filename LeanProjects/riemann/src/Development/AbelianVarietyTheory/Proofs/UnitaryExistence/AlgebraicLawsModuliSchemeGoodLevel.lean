import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralAlgebraicFramedPointExists
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem algebraic_laws_of_good_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ UnitIndep Xo c ∧ IntFrNe Xo c (algCls Xo c) ∧ IntAll Xo c ∧ AllTest Xo c ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), regular₂ Xo c U ∧ CuspMul Xo c U ∧ ((∀ σ, GoodEmb c σ → IsUnf (U σ)) → CuspFD Xo c U ∧ SupDef Xo c U) := by
  intro E _ _ _ H Dw l Xo c hpq hg
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := GlobalTheory.firstFiveLaws.2.1.secTwist
  have hP : PartI := GlobalTheory.T.compactifiedModuli_partOne
  have hA : N1ab := GlobalTheory.Moduli.moduli_scheme_exists
  have hC : N1c := GlobalTheory.closing_of_abelianSchemeLaws
  have h3 := GlobalTheory.Frames.algebraic_laws hS E H Dw l Xo c
  have hR := GlobalTheory.Reg.sCharts_and_transfer_of_good_level hP hA E H Dw l Xo c hpq hg
  refine ⟨h3.2.2.1, h3.2.2.2.2.2.1,
    GlobalTheory.integralAlgebraicFramedPoint_exists hP hA hC hS hT E H Dw l Xo c hpq hg,
    (Formalism.L2.PjFree.intAll_iff Xo c).1 (GlobalTheory.IntegralFrames.intAll hP hA hS hT E H Dw l Xo c hpq hg),
    GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c, fun r U => ⟨?_, ?_, fun hU => ⟨?_, ?_⟩⟩⟩
  · exact (Formalism.L2.PjFree.regP_ofPj U).1 (hR.2.1 r _)
  · exact (Formalism.L2.PjFree.cuspMul_ofPj U).1 (GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c r _)
  · have h0 : GoodEmb c (goodOf c c.F.val.toRingHom) := goodEmb_goodOf c _
    exact (Formalism.L2.PjFree.cuspFD_ofPj U).1
      (GlobalTheory.cuspForms_finiteDimensional_of_isUnf hS E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) _ h0
        ((Formalism.L2.PjFree.isUnf_ofPj (U _)).2 (hU _ h0)))
  · exact (Formalism.L2.PjFree.supDef_ofPj U).1
      (GlobalTheory.supNorm_definite_on_cusp E H Dw l Xo c r _ fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ))

end GlobalTheory.Member
