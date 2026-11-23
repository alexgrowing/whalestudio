import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def ptG (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (i : compL L p)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) :=
  repP L p i * jP I hdet g

def clsG (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (i : compL L p)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    ClassSet ((ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))) :=
  Quotient.mk'' (ptG I hdet i g)

end Formalism.L2.G
