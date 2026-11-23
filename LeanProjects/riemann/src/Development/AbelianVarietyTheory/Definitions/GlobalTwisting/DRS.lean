import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf

noncomputable section

namespace GlobalTheory.Fc

section Def

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S

open GlobalTheory.EX GlobalTheory.EX.OB

abbrev qS {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) :
    RealT b.R b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c) b.S b.B.T.Q.c.F := b.B.Q

def DRS : R1.DefT := fun D O c b C CH =>
  ∀ (hok1 : b.P.A3.fam3.Ok3 1) (hsep : b.P.A3.fam3.TypesSep3)
    (hP : CovolumeOntoIsometryConditions (qS b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) (qS b).sEE (hkCan b.P.A3) C CH) (hI : PassIn3 (qS b).Rl (faceT b.P b.C.toS.c.face b.C.toS.Sp (zsc b.P b.DH.1.1 b.DH.1.2 c)) C CH)
    (lam0 C0 ce Sw C1 : ℝ) (H : ∀ u, (ofRecord D O.L b.DH.1.1 b.DH.1.2).NumFacts (letterOf D O.L b.DH.1.1 b.DH.1.2 u) O.L.Nc lam0 C0 ce c Sw C1)
    (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((b.C.toS.c.face (pkOf (qS b) hok1 hsep C CH hP hI).Zs).a w) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (pkOf (qS b) hok1 hsep C CH hP hI).Zs (pkOf (qS b) hok1 hsep C CH hP hI).core.base.toIndefData
      (pkOf (qS b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (b.C.toS.c.face (pkOf (qS b) hok1 hsep C CH hP hI).Zs)),
    DivTied3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs (pkOf (qS b) hok1 hsep C CH hP hI).Zs (pkOf (qS b) hok1 hsep C CH hP hI).core.base.toIndefData
      (pkOf (qS b) hok1 hsep C CH hP hI).core.cols.toIndefData O.ex.p0 (pkOf (qS b) hok1 hsep C CH hP hI).core.cols.col NuC I →
    HEq I b.P.I → ∀ u, RowsU b.C.toS.c (pkOf (qS b) hok1 hsep C CH hP hI) (RecNums.ofNum (ofRecord D O.L b.DH.1.1 b.DH.1.2) (Equiv.refl _)
          (letterOf D O.L b.DH.1.1 b.DH.1.2 u) (D.mem u).A.T O.L.Nc lam0 C0 ce c Sw C1 (H u)) (I.wU u) (Cons.nuOf O.L u (I.eNu u))

end Def

end GlobalTheory.Fc

end
