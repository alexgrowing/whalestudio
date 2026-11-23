import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnrOff (e : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (e + cA D e) * (x : AE D) = e + cA D e → χ x = 1

def TameAt (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ) : Prop :=
  ∀ (x : (AE D)ˣ) (u : (↥(Formalism.L2.Herm.intAf D.host.F D.host.E))ˣ), (1 - e) * (x : AE D) = 1 - e →
    Datum.toEAf D (x : AE D) = ((u : ↥(Formalism.L2.Herm.intAf D.host.F D.host.E)) : Datum.EAf D) →
    ((χ x : Circle) : ℂ) = ((c (Units.map (Formalism.L2.DIV.resS D.host.F PP).toMonoidHom u) : ℂˣ) : ℂ) ^ k

def stepLev {n : ℕ} (LS : Formalism.L2.DIV.LevDat D.host.E ℂ n)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (m : ℕ) (hm : n ≤ m) :
    Formalism.L2.DIV.LevDat D.host.E ℂ m where
  r := LS.r
  hr := LS.hr.trans hm
  t := LS.t
  s := LS.s + 1
  Pg := LS.Pg
  Q := LS.Q
  P := LS.P
  cg := fun c => if c = LS.s + 1 then χj else LS.cg c
  xq := LS.xq

def thpLev (n r : ℕ) (hr : r ≤ n) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (μ ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n where
  r := r
  hr := hr
  t := n - r
  s := 1
  Pg := Pg
  Q := Q
  P := Formalism.L2.DIV.LevelP.triv Pg r ℂ
  cg := fun _ => μ
  xq := ξ

open Classical in

def VecLawStep (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (Datum.WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ fF : Datum.WO S T → ℂ)
    (hST : S.rank ≤ T.rank),
    Datum.IsWeilDatumO ψ S T χS χT om → WeilFull.SphInertAtO ψ S T χS χT om →
    Datum.IsDatumStep ψ θ S T sS sT BS BT pS pT ΛS ΛT βS βT LS χj Q ξ f₀ fF →
    S.rank = LS.r + LS.s * LS.t → T.rank = S.rank + LS.t → Odd LS.t → LS.Q = Q → LS.xq = (fun PP => (ξ PP)⁻¹) →
    (∀ e, Datum.IsIdemSum e (LS.Pg ∪ Q) → UnrOff e χS ∧ UnrOff e χT) →
    (∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (χj PP) (-1) ∧ TameAt e PP χT (χj PP) (-1)) →
    (∀ PP ∈ Q, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (ξ PP) 1 ∧ TameAt e PP χT (ξ PP) 1) →
    Datum.VecLaw om (Lev.levG S βS LS) (Lev.levChi S βS LS) (Lev.levG T βT (stepLev LS χj T.rank hST))
      (fun κ => (Lev.levChi T βT (stepLev LS χj T.rank hST) κ)⁻¹) fF

open Classical in

def VecLawThP (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (Datum.WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (μ ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ fF : Datum.WO S T → ℂ)
    (hTS : T.rank < S.rank),
    Datum.IsWeilDatumO ψ S T χS χT om → WeilFull.SphInertAtO ψ S T χS χT om →
    Datum.IsDatumThP ψ θ S T sS sT BS BT pS pT ΛS ΛT βS βT Pg Q ξ f₀ fF → Odd (S.rank - T.rank) →
    (∀ e, Datum.IsIdemSum e (Pg ∪ Q) → UnrOff e χS ∧ UnrOff e χT) →
    (∀ PP ∈ Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (μ PP) 1 ∧ TameAt e PP χT (μ PP) 1) →
    (∀ PP ∈ Q, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (ξ PP) 1 ∧ TameAt e PP χT (ξ PP) 1) →
    Datum.VecLaw om (Lev.levG S βS (thpLev S.rank T.rank hTS.le Pg Q μ ξ))
      (fun κ => (Lev.levChi S βS (thpLev S.rank T.rank hTS.le Pg Q μ ξ) κ)⁻¹)
      (Lev.levG T βT (Lev.datW T.rank Pg (Formalism.L2.DIV.LevelP.triv Pg T.rank ℂ) Lev.Frm.B)) (fun _ => 1) fF

open Classical in

def DiagLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (Datum.WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ fF : Datum.WO S T → ℂ)
    (hST : S.rank ≤ T.rank),
    Datum.IsWeilDatumO ψ S T χS χT om → WeilFull.SphInertAtO ψ S T χS χT om →
    Datum.IsDatumStep ψ θ S T sS sT BS BT pS pT ΛS ΛT βS βT LS χj Q ξ f₀ fF →
    S.rank = LS.r + LS.s * LS.t → T.rank = S.rank + LS.t → Odd LS.t → LS.Q = Q → LS.xq = (fun PP => (ξ PP)⁻¹) →
    LS.P = Formalism.L2.DIV.LevelP.triv LS.Pg LS.r ℂ →
    (∀ e, Datum.IsIdemSum e (LS.Pg ∪ Q) → UnrOff e χS ∧ UnrOff e χT) →
    (∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (χj PP) (-1) ∧ TameAt e PP χT (χj PP) (-1)) →
    (∀ PP ∈ Q, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP → TameAt e PP χS (ξ PP) 1 ∧ TameAt e PP χT (ξ PP) 1) →
    ∀ κS ∈ Lev.levG S βS (Lev.flagL LS), ∀ κT ∈ Lev.levG T βT (Lev.flagL (stepLev LS χj T.rank hST)),
      Formalism.L2.DIV.rTup βS LS (Lev.finE S κS) = Formalism.L2.DIV.rTup βT (stepLev LS χj T.rank hST) (Lev.finE T κT) →
      om (κS, κT) fF = (Lev.levChi S βS (Lev.flagL LS) κS *
        (Lev.levChi T βT (Lev.flagL (stepLev LS χj T.rank hST)) κT)⁻¹) • fF

end Formalism.IndefR.Fin

end
