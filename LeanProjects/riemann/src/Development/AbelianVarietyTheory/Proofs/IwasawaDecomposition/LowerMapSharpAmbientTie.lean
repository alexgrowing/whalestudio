import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Formalism.LocalToGlobal.Divisibility.TupUsed
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem lower_map_sharp_ambient_tie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (T : TiedDataSK ex), (∀ u, LowerMapTieS (T.cols.forms u)) → (∀ u μ (hμ : μ ≠ D.what₂.mu0) (_ : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), LowerMapTieTw T u μ hμ h1) → (∃ J, AmbTie D x.A3.A (RowSide.sharp D) ex.amb x.F.P1 x.F.ψ1 x.Y.tup x.Y.jA J) → ((∀ (t : x.T) (c : (x.A3.A.fam.R t).S.Cl), Fintype.card ((x.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧ ∀ (j : Fin D.R.m) (t : x.T) (c : (x.A3.A.fam.L j t).S.Cl), Fintype.card ((x.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) → RowSideDetermined T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro D L hT Gi Gl K Yd cX ex x T hL hLt hA hG
  exact
    { lowerMap := hL
      lowerMapTw := hLt
      buDef := x.Y.bu
      ambS := hA
      faces := ⟨x.F.Dc, x.F.Sp, rfl, HEq.rfl⟩
      gamDvd := hG }

end GlobalTheory.Mem.R3
