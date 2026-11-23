import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace Formalism.IndefR.RationalEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev inst : Formalism.MainNotions.S.AutInst := Formalism.L2.SG.InstExistsPf.instOf D

def iota : GA D (D.sp.Y 0) ≃ₜ* (inst D).GA :=
  (Formalism.L2.SG.AdBridge.toHA (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1).symm

theorem iota_symm_isBridge : Formalism.L2.SG.AdBridge.IsBridge (inst D) (iota D).symm :=
  Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1

theorem iota_rat (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iota D g ∈ (inst D).GFset := by
  have hS := Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)
  have hb := Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) hS.1
  have hGF := hS.2.1 _ hb
  have hg : Formalism.L2.SG.AdBridge.toHA (inst D) hS.1 (iota D g) = g :=
    (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).apply_symm_apply g
  rw [← (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).injective.mem_set_image (a := iota D g)
    (s := (inst D).GFset), hGF, hg]
  exact Iff.rfl

end Formalism.IndefR.RationalEmbedding

end
