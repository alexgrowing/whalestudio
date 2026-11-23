import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Mv (D : D7) : Type 1 where
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ
  dsig : D.what₂.Tau → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ
  s : Formalism.MainNotions.S.Draft.SData D.R (↥D.host.F) D.host.E D.conjF D.what₂.Word D.what₂.Tau D.hcW
  s_split : ∀ p : HeightOneSpectrum (𝓞 ↥D.host.F),
    (s.atP p).split.isSome = true ↔ Formalism.MainNotions.S.Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)
  s_HH : Module.finrank ℂ s.HH = D.what₂.Dall
  s_Cu : (u : D.what₂.Word) → s.Cu u ≃ₗ[ℂ] ↥(D.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 ↥D.host.F)
  s_Cu_isom : ∀ (u : D.what₂.Word) (x y : s.Cu u), inner ℂ x y = (D.fm u).ipC 0 ↑((s_Cu u) x) ↑((s_Cu u) y)
  sEE : D.what₂.EE →ₗᵢ⋆[ℂ] s.HH

abbrev Mv.D {D : D7} (m : Mv D) : D7 :=
  { (setDiv D m.N m.h) with
    dsig := m.dsig
    dsig_pos := m.dsig_pos
    s := m.s
    s_split := m.s_split
    s_HH := m.s_HH
    s_Cu := m.s_Cu
    s_PlF := m.s_PlF
    s_Cu_isom := m.s_Cu_isom
    sEE := m.sEE }

section
variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (S' : SStage B w.C Z.W)
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

def mvOf : Mv (w.D Z) :=
  ⟨N, h, (w.D (upL Z S' N h)).dsig, (w.D (upL Z S' N h)).dsig_pos, (w.D (upL Z S' N h)).s, (w.D (upL Z S' N h)).s_split,
    (w.D (upL Z S' N h)).s_HH, (w.D (upL Z S' N h)).s_Cu, (w.D (upL Z S' N h)).s_PlF, (w.D (upL Z S' N h)).s_Cu_isom,
    (w.D (upL Z S' N h)).sEE⟩

end

variable {D : D7} (m : Mv D)

def Mv.pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) : Mv D₀ :=
  { N := (by with_unfolding_all exact (m.N :))
    h := (by with_unfolding_all exact (m.h :))
    dsig := (by with_unfolding_all exact (m.dsig :))
    dsig_pos := (by with_unfolding_all exact (m.dsig_pos :))
    s := (by with_unfolding_all exact (m.s :))
    s_split := (by with_unfolding_all exact (m.s_split :))
    s_HH := (by with_unfolding_all exact (m.s_HH :))
    s_Cu := (by with_unfolding_all exact (m.s_Cu :))
    s_PlF := (by with_unfolding_all exact (m.s_PlF :))
    s_Cu_isom := (by with_unfolding_all exact (m.s_Cu_isom :))
    sEE := (by with_unfolding_all exact (m.sEE :)) }

def Mv.loc (L : LocAll (lay0 D)) : LocAll (lay0 m.D) := (by with_unfolding_all exact (L :))

theorem Mv.withLoc_pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) : m.D = withLoc (m.pre.loc L) := (by with_unfolding_all exact ((Eq.refl m.D) :))

def Mv.cf (cf : CharFrame D) : CharFrame m.D :=
  { P := (by with_unfolding_all exact (cf.P :))
    W := (by with_unfolding_all exact (cf.W :))
    mu0 := (by with_unfolding_all exact (cf.mu0 :))
    eta := (by with_unfolding_all exact (cf.eta :))
    chiPsi := (by with_unfolding_all exact (cf.chiPsi :))
    del := (by with_unfolding_all exact (cf.del :))
    del' := (by with_unfolding_all exact (cf.del' :))
    isMu0 := (by with_unfolding_all exact (cf.isMu0 :))
    isEta := (by with_unfolding_all exact (cf.isEta :))
    isChi := (by with_unfolding_all exact (cf.isChi :))
    isDel := (by with_unfolding_all exact (cf.isDel :))
    isDel' := (by with_unfolding_all exact (cf.isDel' :)) }

def Mv.ch (C : NChoice D) : NChoice m.D := { C with }

def Mv.xd (x : ThData D) : ThData m.D := { x with }

def Mv.tp {cf : CharFrame D} {C : NChoice D} (tp : TupTied D cf C) : TupTied m.D (m.cf cf) (m.ch C) :=
  { xi := (by with_unfolding_all exact (tp.xi :))
    xi_inj := (by with_unfolding_all exact (tp.xi_inj :))
    xi_fin := (by with_unfolding_all exact (tp.xi_fin :))
    xi_triv := (by with_unfolding_all exact (tp.xi_triv :))
    xi_tame := (by with_unfolding_all exact (tp.xi_tame :))
    psi := (by with_unfolding_all exact (tp.psi :))
    trueColumnChoices_heckeChar_reference_eq_one := (by with_unfolding_all exact (tp.trueColumnChoices_heckeChar_reference_eq_one :))
    xi_star := (by with_unfolding_all exact (tp.xi_star :))
    xi_star' := (by with_unfolding_all exact (tp.xi_star' :))
    xi_tw := (by with_unfolding_all exact (tp.xi_tw :))
    psi_is := (by with_unfolding_all exact (tp.psi_is :))
    psi_un := (by with_unfolding_all exact (tp.psi_un :)) }

def Mv.mt (M : Formalism.L2.MtFam D) : Formalism.L2.MtFam m.D := @fun x1 => @fun x2 => @fun x3 => @fun x4 =>
  { wt := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).wt : _))
    J := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).J : _))
    χ := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).χ : _))
    J_open := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).J_open : _))
    real := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).real : _))
    real_inj := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).real_inj : _))
    real_range := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).real_range : _)) }

end GlobalTheory.LayerMove
end
