import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Nonempty (Comp Xo c) ∧ Finite (Comp Xo c) ∧ ∃ h : GenFrEx Xo c, GenFromTest Xo c h ∧ (∀ Z, evC h Z 1 = 1) ∧ ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c h1
  have hB : Out.SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.allSixLaws.2.1.secTwist
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have h : GenFrEx Xo c := genFrEx_of hT
  have hg : GenFromTest Xo c h := fun Z => hA _ _
  obtain ⟨x⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2 GlobalTheory.closing_of_abelianSchemeLaws h1 l Xo c
  exact ⟨⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩,
    CompFin.finite_comp Xo c, h, hg, fun Z => evalAt_one _ _ _ (hg Z),
    (GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2⟩
