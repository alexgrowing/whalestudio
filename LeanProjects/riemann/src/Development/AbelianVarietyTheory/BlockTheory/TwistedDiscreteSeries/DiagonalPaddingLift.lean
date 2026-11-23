import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPaddingLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def padOne {R : Type} [Zero R] [One R] {r n : ℕ} (_hr : r ≤ n) (k : Matrix (Fin r) (Fin r) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if h : i.val < r ∧ j.val < r then k ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else if i = j then 1 else 0

def IsDiagLift {D : D7} (e : AE D) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (PP : Formalism.L2.DIV.Pl D.host.E) {r : ℕ}
    (hr : r ≤ V.rank) (k : GL (Fin r) (Formalism.L2.DIV.kP PP)) (κ : GA D V) : Prop :=
  SuppAt e V κ ∧ Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧
    ((Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V κ) : GL (Fin V.rank) (Formalism.L2.DIV.kP PP)) :
      Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)) =
      padOne hr (k : Matrix (Fin r) (Fin r) (Formalism.L2.DIV.kP PP))

def StepVecDiagInvariant : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hST : S.rank ≤ T.rank)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ),
    IsWeilDatumO ψ S T χS χT om →
    Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    LS.P = Formalism.L2.DIV.LevelP.triv LS.Pg LS.r ℂ →
    Disjoint LS.Pg Q →
    IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f →
    ∀ PP ∈ LS.Pg, ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP →
    ∀ (k : GL (Fin LS.r) (Formalism.L2.DIV.kP PP)) (κ : GA D S) (κ' : GA D T),
      IsDiagLift e S βS PP LS.hr k κ → IsDiagLift e T βT PP (LS.hr.trans hST) k κ' →
      ∀ x y : (AE D)ˣ, IsDetAt e S κ x → IsDetAt e T κ' y → χT x = χS y →
        om (κ, κ') f = f

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPaddingLift

end
