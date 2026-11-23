import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.NormCut

section Phase

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

def scOf {u : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u rs) (ρ : c.Cl) :
    Iof TR :=
  levi TR (((c.h (c.base (c.lamOf ρ)) : X.B.I.Gf) * X.xu u)⁻¹ * ((c.h ρ : X.B.I.Gf) * X.xu u))

def Aset {u : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u rs)
    (q : {Λ // Λ ∈ rs}) : Set (Iof TR) :=
  {x | ∃ γ : Formalism.L2.SG.PoincareInHH.PoincareSetting.Gam X u,
    ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u γ : X.B.I.Gf) *
        ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset ∧
      x = levi TR (((c.h (c.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ *
        (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u γ : X.B.I.Gf) * ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u))}

variable {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def LeviCols : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    levi TR (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) =
      (scOf TR cs ρ)⁻¹ * iotaOf TR cs cs' t * scOf TR cs' ρ'

variable (F0 F0') in

def PhaseAt : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    (if kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2 then
      chiL X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) else 0) =
    psiG TR (levi TR (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt))

theorem colPhase_of (hL : LeviCols TR F0 F0' cs cs') (hP : PhaseAt TR F0 F0' cs cs') :
    ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  intro t ρ ρ' hρ hρ'
  rw [hP t ρ ρ' hρ hρ', hL t ρ ρ' hρ hρ']

end Phase

end Formalism.L2.SG.NormCut
