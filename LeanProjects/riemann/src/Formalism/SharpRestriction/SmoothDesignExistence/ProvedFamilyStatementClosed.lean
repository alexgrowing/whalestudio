import Formalism.LocalToGlobal.GroupLattices.AdmissibleFamilyNoKernel
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrvAndKernelCommutationUpToUnitsOfRests
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumFEx
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.SharpRestriction.GrowthBounds.JointsLit
import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.DivisionRationalLattice

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

structure FamilyClassHypotheses (𝒞 : FamClass) : Prop where

  arithLevel : Closed 𝒞 fun Fm _ => EvD Fm fun D => ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), J.ArithLevel D (D.gat u w hg)

  finClasses : Closed 𝒞 fun Fm _ => EvD Fm fun D => ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), (D.gat u w hg).FinClasses

  stdSub : Closed 𝒞 fun Fm _ => G.Ev Fm fun x i => G.Joints.StdSubAt (Fm.D x i)

  npDesc : Closed 𝒞 fun Fm _ => G.NPDescF Fm

end Formalism.MainNotions.Pk

end
