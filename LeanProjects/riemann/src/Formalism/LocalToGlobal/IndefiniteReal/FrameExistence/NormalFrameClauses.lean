import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg2
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistGOfFramesExist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def XBasesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) : Prop :=
  ∀ j : ℕ, j < D.R.m → ∃ βX : GL (Fin (D.sp.X j).rank) (EAf D), Formalism.L2.DIV.IsFrame βX (l0X (D.sp.X j)) ∧
    ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ (col : Fin (D.sp.Y j).rank) (l : Fin (D.sp.X j).rank), IsXCol (D := D) j col l →
        ∀ r : Fin (D.sp.Y j).rank, toEAf D ei * (betaYOf βY j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => βX.val i l) r

def NormalFrameConditionsDiagonal (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  NormalClausesG Pg βY βW ∧ XBasesG Pg βY

variable (D) in

def FramesExistDiagonal (Pg : Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalFrameConditionsDiagonal Pg βY βW

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem framesOKg2_iff (Rl : RealDat3 D A3 Ks) :
    FramesOKg2 Rl ↔ NormalFrameConditionsDiagonal Rl.toRealDat.Pg Rl.toRealDat.βY Rl.toRealDat.βW := by
  first
  | exact Iff.rfl
  | (unfold FramesOKg2 NormalFrameConditionsDiagonal; done)

end Formalism.IndefR.Seed.Frm

end
