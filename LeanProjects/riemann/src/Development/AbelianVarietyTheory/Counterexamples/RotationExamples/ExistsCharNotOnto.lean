import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.RealIndexBoundProbe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def withTup (R : RealDat D A Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T)
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (e : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) :
    RealDat D A Ks :=
  { R with mu := mu, twPl := tw, err0 := e }

abbrev withErr (R : RealDat D A Ks) (e : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) : RealDat D A Ks :=
  withTup R R.mu R.twPl e

variable {R : RealDat D A Ks} {F : Face D A}

set_option maxHeartbeats 2000000 in

theorem char_withTup (h : R.Char F) {mu tw e} (ht : (withTup R mu tw e).IsTup F) : (withTup R mu tw e).Char F where
  lev := h.lev
  grp := ⟨h.grp.red_R, h.grp.red_L, h.grp.levels, h.grp.record, h.grp.chiW⟩
  fam := ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩
  models := ⟨h.models.inf, h.models.vpos, h.models.cX, h.models.cV, h.models.prX, h.models.HX, h.models.HV, h.models.HE,
    h.models.HW, h.models.gE, h.models.gW, h.models.jX, h.models.jV, h.models.νY, h.models.νY', h.models.ν0, h.models.νX,
    h.models.νV, h.models.νW, h.models.BV, h.models.order⟩
  chain := ⟨h.chain.ωY, h.chain.ωX, h.chain.vY, h.chain.vX, h.chain.ptY, h.chain.ptX, h.chain.ItY, h.chain.ItX,
    h.chain.ioY, h.chain.ioX, h.chain.Th⟩
  thP := ⟨h.thP.ωP, h.thP.vP, h.thP.pt_theta, h.thP.ioP, h.thP.thF_mem, h.thP.thF, h.thP.thG⟩
  scal := ⟨h.scal.lam0, h.scal.kap, h.scal.lam_off, h.scal.zero_part_eigenvalue_abs, h.scal.lam_abs, h.scal.lam_tup⟩
  tup := ht

set_option maxHeartbeats 1000000 in
theorem withTup_nonzeroIndexPlace_iff {mu tw e} (w) : (withTup R mu tw e).NonzeroIndexPlace F w ↔ R.NonzeroIndexPlace F w := Iff.rfl

theorem char_withErr (h : R.Char F) (e) : (withErr R e).Char F :=
  char_withTup h ⟨fun w hw => h.tup.tw w ((withTup_nonzeroIndexPlace_iff w).1 hw), h.tup.mu_off, h.tup.mu_used, h.tup.mu_ne, h.tup.mu_conj, h.tup.mu_on⟩

theorem not_onto_neg {w} (hw : w ∈ R.twPl) (j : Fin D.R.m) (C CH : ℝ) : ¬ (withErr R fun _ _ => -1).LOnto F C CH := by
  intro h
  have := h.2.1 w hw j
  have h2 : (0 : ℝ) ≤ -1 := this
  linarith

theorem exists_char_not_onto (h : R.Char F) {w} (hw : w ∈ R.twPl) (j : Fin D.R.m) :
    ∃ R' : RealDat D A Ks, R'.Char F ∧ R'.mu = R.mu ∧ R'.twPl = R.twPl ∧ ∀ C CH, ¬ R'.LOnto F C CH :=
  ⟨withErr R fun _ _ => -1, char_withErr h _, rfl, rfl, not_onto_neg hw j⟩

end GlobalTheory.RealIndexBoundProbe

end
