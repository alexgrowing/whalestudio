import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalisedAdaptedVectorZero
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Links Formalism.IndefR.Lev

variable {D : D7}

theorem frames_by_cases {T : Type} (hSD : FrmP.SDFramesExist D) (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E)) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
      (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
      (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
      (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
      (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
      (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
      SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ (FramesExist D Pg Sd Q → NormalClauses Pg Sd Q βY βW) := by
  by_cases h : FramesExist D Pg Sd Q
  · obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, h1, h2⟩ := h
    exact ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, h1, fun _ => h2⟩
  · obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, h1⟩ := hSD
    exact ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, h1, fun h' => absurd h' h⟩

theorem frames_by_cases_std {T : Type} (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, FrmC.StdLat (D.sp.W j))
    (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E)) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
      (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
      (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
      SDFrames ΛY (FrmP.coordL D.sp.X') (fun i => FrmP.coordL (Vc D i)) ΛW βY 1 (fun _ => 1) βW ∧
        (FramesExist D Pg Sd Q → NormalClauses Pg Sd Q βY βW) := by
  by_cases h : FramesExist D Pg Sd Q
  · obtain ⟨ΛY, -, -, ΛW, βY, -, -, βW, ⟨h1, -, -, h4⟩, h2⟩ := h
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1, h4⟩, fun _ => h2⟩
  · exact ⟨fun j => FrmP.coordL (Yc D j), fun i => FrmP.coordL (Wc D i), fun _ => 1, fun _ => 1,
      ⟨fun j _ => FrmP.isSDFrame_std _ (hY _) _, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1,
        fun i => FrmP.isSDFrame_std _ (hW _) 1⟩, fun h' => absurd h' h⟩

end Formalism.IndefR.Seed.Frm

end
