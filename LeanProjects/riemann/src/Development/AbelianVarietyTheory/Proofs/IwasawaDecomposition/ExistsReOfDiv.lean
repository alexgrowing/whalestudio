import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SIsoReD
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

section Trans

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def LocIso.trans {A B C : Formalism.MainNotions.S.Loc.LocAt F E sig p} (a : Formalism.L2.S.LocIso A B) (b : Formalism.L2.S.LocIso B C) :
    Formalism.L2.S.LocIso A C where
  eF := a.eF.trans b.eF
  eF_ι x := (congrArg b.eF (a.eF_ι x)).trans (b.eF_ι x)
  eF_val x y := (a.eF_val x y).trans (b.eF_val _ _)
  eF_cont := b.eF_cont.comp a.eF_cont
  eF_symm_cont := a.eF_symm_cont.comp b.eF_symm_cont
  eF_ql x := (congrArg b.eF (a.eF_ql x)).trans (b.eF_ql x)
  eE := a.eE.trans b.eE
  eE_alg x := (congrArg b.eE (a.eE_alg x)).trans (b.eE_alg _)
  eE_ι x := (congrArg b.eE (a.eE_ι x)).trans (b.eE_ι x)
  eE_cont := b.eE_cont.comp a.eE_cont
  eE_symm_cont := a.eE_symm_cont.comp b.eE_symm_cont
  eE_cj y := (congrArg b.eE (a.eE_cj y)).trans (b.eE_cj _)
  eE_O y := (a.eE_O y).trans (b.eE_O _)
  eE_psi y := (a.eE_psi y).trans (b.eE_psi _)

variable {R : Ranks} {Word Tau : Type} {hc : Word → Tau → HCParam R}

def SIso.trans {s s' s'' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc} (a : SIso s s') (b : SIso s' s'') : SIso s s'' where
  cd := a.cd.trans b.cd
  del := a.del.trans b.del
  letter := a.letter.trans b.letter
  eHH := a.eHH.trans b.eHH
  eCu u := (a.eCu u).trans (b.eCu u)
  Pu_eq u x := (congrArg b.eHH (a.Pu_eq u x)).trans (b.Pu_eq u _)
  volN := a.volN.trans b.volN
  volH := a.volH.trans b.volH
  eT u u' := (a.eT u u').trans (b.eT u u')
  aTerm_eq u u' t x := (congrArg (b.eCu u) (a.aTerm_eq u u' t x)).trans (b.aTerm_eq u u' _ _)
  isId t := (a.isId t).trans (b.isId _)
  inS t := (a.inS t).trans (b.inS _)
  relevant t := (a.relevant t).trans (b.relevant _)
  FeqF t := (a.FeqF t).trans (b.FeqF _)
  Gterm t := (a.Gterm t).trans (b.Gterm _)
  atP p := LocIso.trans (a.atP p) (b.atP p)
  ePl := a.ePl.trans b.ePl
  BBne t q := (a.BBne t q).trans (b.BBne _ _)
  generic t := (a.generic t).trans (b.generic _)
  eP u u' := (a.eP u u').trans (b.eP u u')
  pfst p := (congrArg (b.eT _ _) (a.pfst p)).trans (b.pfst _)
  psnd p := (congrArg (b.eT _ _) (a.psnd p)).trans (b.psnd _)
  s0 p := (a.s0 p).trans (b.s0 _)
  scalarPair p := (a.scalarPair p).trans (b.scalarPair _)
  pval p := (a.pval p).trans (b.pval _)
  ptOf t := (a.ptOf t).trans (b.ptOf _)
  cTerm t := (a.cTerm t).trans (b.cTerm _)
  massPair p := (a.massPair p).trans (b.massPair _)
  meanCount := a.meanCount.trans b.meanCount

end Trans

section Move

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)

theorem SRest.exists_re_ofDiv {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P)
    {F' : ∀ u, Forms0 (reD D (New.ofDiv D N hh)) u} (h : SameForms0LevelsAndValues (New.ofDiv D N hh) F F')
    (hF : FinX (reY (New.ofDiv D N hh) P.Y)) :
    ∃ S' : SRest (P.re (New.ofDiv D N hh) h hF), HEq S'.j S.j := by
  obtain ⟨e, heH, heC⟩ := sIso_reD D (New.ofDiv D N hh) P.X P.Y P.fin hF
  let hI' : SIso (reD D (New.ofDiv D N hh)).s (sOf (P.re (New.ofDiv D N hh) h hF).fin) := (by with_unfolding_all exact (SIso.trans S.hI e :))
  let aT : Formalism.MainNotions.S.AutTie (reD D (New.ofDiv D N hh)) (P.re (New.ofDiv D N hh) h hF).X.B
      (P.re (New.ofDiv D N hh) h hF).X.pl :=
    ⟨(by with_unfolding_all exact (S.autTie.n_eq :)), (by with_unfolding_all exact (S.autTie.f_eq :)), (by with_unfolding_all exact (S.autTie.rd_eq :)), (by with_unfolding_all exact (S.autTie.eps_eq :)),
      (by with_unfolding_all exact (S.autTie.lam_eq :)), (by with_unfolding_all exact (S.autTie.ds :)), (by with_unfolding_all exact (S.autTie.low :)), (by with_unfolding_all exact (S.autTie.g_eq :)),
      (by with_unfolding_all exact (S.autTie.g0_eq :)), (by with_unfolding_all exact (S.autTie.D_eq :)), (by with_unfolding_all exact (S.autTie.Dstar_eq :))⟩
  let jj : (reD D (New.ofDiv D N hh)).what₂.EE ≃ₗᵢ[ℂ] EEC (P.re (New.ofDiv D N hh) h hF).X
      (P.re (New.ofDiv D N hh) h hF).G := (by with_unfolding_all exact (S.j :))
  have lT : Formalism.L2.SG.Pf.LocCP.LocTied (reD D (New.ofDiv D N hh)) := (by with_unfolding_all exact (S.locTied :))
  have cP : ∀ (u : (reD D (New.ofDiv D N hh)).what₂.Word) (x : (reD D (New.ofDiv D N hh)).s.Cu u),
      colDict (P.re (New.ofDiv D N hh) h hF).X ((P.re (New.ofDiv D N hh) h hF).tr u)
        (P.re (New.ofDiv D N hh) h hF).Y.hK ((P.re (New.ofDiv D N hh) h hF).into u)
        ((P.re (New.ofDiv D N hh) h hF).bij u) (hI'.eCu u x) = (reD D (New.ofDiv D N hh)).s_Cu u x := by
    intro u x
    have hx : hI'.eCu u x = ((by with_unfolding_all exact (S.hI.eCu u x :))) := (by with_unfolding_all exact (congrArg (fun f => f (S.hI.eCu u x)) (eq_of_heq (heC u)) :))
    rw [hx]
    apply Subtype.ext
    exact (by with_unfolding_all exact ((colDictL_reTr (New.ofDiv D N hh) (P.tr u) (h u).2.1 (h u).2.2 P.Y.hK
      (toCu (cs := P.Y.cs u) (hinj := P.fin.shInj u) P.X P.Y.hK (S.hI.eCu u x))).trans (congrArg Subtype.val (S.colPin u x)) :))
  have rP : ∀ x : (reD D (New.ofDiv D N hh)).what₂.EE,
      hI'.eHH ((reD D (New.ofDiv D N hh)).sEE x) =
        conjHH (P.re (New.ofDiv D N hh) h hF).X (P.re (New.ofDiv D N hh) h hF).G (jj x) := by
    intro x
    exact (by with_unfolding_all exact ((congrArg (fun f => f (S.hI.eHH (D.sEE x))) (eq_of_heq heH)).trans (S.rowPin x) :))
  exact ⟨⟨hI', aT, cP, jj, rP, lT⟩, (by with_unfolding_all exact (HEq.refl S.j :))⟩

end Move

end GlobalTheory.Mem.SRe

end
