import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

def indefiniteDataAtBaseLevel (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    IndefRows (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false) :=
  X.rowsOfR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.rowHyp false) hR.liftHyp0 (hR.pos false) hR.proviso0
    hR.types0 hR.h0
    (CxData.cutDims X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.wf false) hR.h4pos hR.kForm hR.ewNorm hR.types0
      (hR.what₂ false).1 (hR.ratMu false) (hR.rowHyp false).h3 hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W (hR.partsE false)
      hR.partsW hR.dimParts)

theorem subspaces_stable_in_block (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.zs.Stable ∧ X.zs.InBlock :=
  ⟨hR.stable, hR.inBlock⟩

end Formalism.IndefR.Cx
