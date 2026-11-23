import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FrmCase

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def NormalClausesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (NormalFrames (betaYOf βY) e ev z κ s Pg Pg ∧ NormalFrame0 (betaYOf βY 0) Pg Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg

variable (D) in

def FramesExistG (Pg : Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalClausesG Pg βY βW

theorem frames_by_cases_stdG (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, FrmC.StdLat (D.sp.W j)) (Pg : Finset (Pl D.host.E)) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
      (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
      (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
      SDFrames ΛY (FrmP.coordL D.sp.X') (fun i => FrmP.coordL (Vc D i)) ΛW βY 1 (fun _ => 1) βW ∧
        (FramesExistG D Pg → NormalClausesG Pg βY βW) := by
  classical
  have hXs : IsSDFrame D.sp.X' 1 (FrmP.coordL D.sp.X') 1 := FrmP.isSDFrame_std D.sp.X' hX 1
  have hVs : ∀ i, IsSDFrame (Vc D i) 1 (FrmP.coordL (Vc D i)) 1 := fun i => FrmP.isSDFrame_std (Vc D i) (hV _) 1
  by_cases hG : FramesExistG D Pg
  · obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, ⟨h1, -, -, h4⟩, hN⟩ := hG
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, hXs, hVs, h4⟩, fun _ => hN⟩
  · obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, ⟨h1, -, -, h4⟩⟩ := FrmP.sdFramesExist_of_std hY hX hV hW
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, hXs, hVs, h4⟩, fun h => absurd h hG⟩

open Classical in

theorem framesExistG_of_framesExist {T : Type} (t0 : T) {Pg : Finset (Pl D.host.E)}
    (h : FramesExist D Pg ∅ (fun _ : T => ∅)) : FramesExistG D Pg := by
  obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, hSD, e, ev, z, κ, s, hN, hW⟩ := h
  have h0 := hN t0
  simp only [Finset.union_empty] at h0
  exact ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, hSD, e, ev, z, κ, s, h0, hW⟩

end Formalism.IndefR.Seed.Frm

end
