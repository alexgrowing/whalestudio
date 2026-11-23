import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QPlacesOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesMembershipTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellQPlacesOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharacStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.XPara

theorem paraShape_export : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  intro hPr hL
  refine (StepW.and (GlobalTheory.T.q_places_of_admissible_twist hPr hL) (StepW.and (GlobalTheory.T.cell_places_of_admissible_twist hPr hL) (StepW.and (GlobalTheory.T.cell_places_membership_twist hPr hL)
    (StepW.and (GlobalTheory.T.reads_hecke_of_side_read hPr hL) (StepW.and (GlobalTheory.T.reads_hecke_of_side_read_cell hPr hL) (GlobalTheory.T.cell_q_places_of_admissible_twist hPr hL)))))).trans
    (StepW.of_all fun K B f T w _ _ H P x l v i b ψ hA j htw hl hok e hS hR => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  intro u hu
  obtain ⟨P', hP', hPu⟩ := h1 P x l v i b ψ hA j htw hl hok u hu
  obtain ⟨hex, hg, hq, hd⟩ := h2 P x l v i b ψ hA j htw hl hok P' hP'
  obtain ⟨hwq, hwd⟩ := h6 P x l v i b ψ hA j htw hl hok
  have hT := h3 P x l v i b ψ hA j htw hl hok P' hP'
  have hw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').w = P' :=
    (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (hP'.elim Or.inl fun h => Or.inr (Or.inl h))
  rw [← hw] at hT
  obtain ⟨ξ, hξc, hξv⟩ := GlobalTheory.HeckeSplitComp.main _ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P') _ hT
  refine ⟨(cell (D := Dof x) l.b.Bs.exp b hA j).sp P', ξ, hPu, hξc, ?_⟩
  have hne : ∀ a : 𝓞 (Dof x).host.E, a ∉ P'.asIdeal → (a : (Dof x).host.E) ≠ 0 := fun a ha h0 =>
    ha (by rw [show a = 0 from by exact_mod_cast h0]; exact Ideal.zero_mem _)
  refine GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter _ _ _ _ _ _ _ _ _ _ _ _ e P' ξ hP' hex hg hq hd hwq hwd ?_ ?_
  · intro hq' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h4 P x l v i b ψ hA j htw hl hok e hS hR P' hq' a _ ha rfl).symm
  · intro hd' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h5 P x l v i b ψ hA j htw hl hok e hS hR P' hd' a _ ha rfl).symm

end GlobalTheory.XPara

end
