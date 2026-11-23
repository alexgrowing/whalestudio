import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsU
import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsPack
import Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem unitSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : UnitSelfSt Y p :=
  unitSelf_of Y p fun o => gmPack_holds Y (p o)

theorem projSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : ProjSelfSt Y p :=
  projSelf_of Y p fun o => gmPack_holds Y (p o)

theorem germLiftSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
    (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : GermLiftSelfSt Y p H :=
  germLiftSelf_of Y p H (projSelf_holds Y p) fun o => tcoordSelf_holds C V O dd Y d (I0 o) (p o) (H o).cartH

end Formalism.L2.FormalSeriesBounds
