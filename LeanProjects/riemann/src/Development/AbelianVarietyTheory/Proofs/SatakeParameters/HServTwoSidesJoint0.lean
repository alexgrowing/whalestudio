import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.hServTwoSidesJoint0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (C : ColsTiedSym D) (full : ColsFullS C), g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → ∀ u, Joint0 g.herm.lev0 u (g.forms u) := by
  intro D Gt c g C full hh hf u
  rw [hh, hf]
  have e : full.1.to0.lev0 = C.herm.base.lev0 :=
    congrArg (fun X : Formalism.L2.Herm.ColsHermS D => X.base.lev0) full.2
  rw [e]
  exact C.joint0 u
