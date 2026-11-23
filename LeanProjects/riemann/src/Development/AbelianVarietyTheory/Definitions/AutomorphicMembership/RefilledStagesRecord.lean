import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

structure SNew (D : D7) : Type 1 where
  s : Formalism.MainNotions.S.Draft.SData D.R D.host.F D.host.E D.conjF D.what₂.Word D.what₂.Tau D.hcW
  s_HH : Module.finrank ℂ s.HH = D.what₂.Dall
  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (D.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 D.host.F)
  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (D.fm u).ipC 0 ((s_Cu u x : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
  sEE : D.what₂.EE →ₗᵢ⋆[ℂ] s.HH

def mix {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {Word Tau : Type} {hc : Word → Tau → HCParam R} (s t : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc :=
  { t with
    cdScale := s.cdScale, cdScale_pos := s.cdScale_pos, Del := s.Del, Del_pos := s.Del_pos, cloud_gap := s.cloud_gap
    letter := s.letter, letter_inj := s.letter_inj, u_letter := s.u_letter, atP := s.atP }

def reS (D : D7) (Z : SNew D) : D7 :=
  { D with
    s := mix D.s Z.s
    s_split := D.s_split
    s_HH := Z.s_HH
    s_Cu := Z.s_Cu
    s_PlF := Z.s_PlF
    s_Cu_isom := Z.s_Cu_isom
    sEE := Z.sEE }

def SNew.self (D : D7) : SNew D := ⟨D.s, D.s_HH, D.s_Cu, D.s_PlF, D.s_Cu_isom, D.sEE⟩

theorem reS_self (D : D7) : reS D (SNew.self D) = D := rfl

def reStage (X : Stages) (Z : SNew X.toD7) : SStage X.B X.C X.W where
  dsig := X.S.dsig
  dsig_pos := X.S.dsig_pos
  s := mix X.S.s Z.s
  s_split := X.S.s_split
  s_HH := Z.s_HH
  s_Cu := Z.s_Cu
  s_PlF := Z.s_PlF
  s_Cu_isom := Z.s_Cu_isom
  sEE := Z.sEE

def reStages (X : Stages) (Z : SNew X.toD7) : Stages := { X with S := reStage X Z }

theorem refilledStages_record (X : Stages) (Z : SNew X.toD7) : (reStages X Z).toD7 = reS X.toD7 Z := rfl

section
variable (D : D7) (Z : SNew D)

theorem reS_atP : (reS D Z).s.atP = D.s.atP := rfl
theorem reS_Del : (reS D Z).s.Del = D.s.Del := rfl
theorem reS_letter : (reS D Z).s.letter = D.s.letter := rfl
theorem reS_cdScale : (reS D Z).s.cdScale = D.s.cdScale := rfl
theorem reS_dsig : (reS D Z).dsig = D.dsig := rfl
theorem reS_rows : (reS D Z).what₂ = D.what₂ := rfl
theorem reS_HH : (reS D Z).s.HH = Z.s.HH := rfl

end

end GlobalTheory.Mem.SRe

end
