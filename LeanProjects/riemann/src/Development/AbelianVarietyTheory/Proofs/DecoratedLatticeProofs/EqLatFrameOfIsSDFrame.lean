import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColTOfPinColL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd
open GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

abbrev lineZ (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem gram_X' {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) : (I.rec7 l Z).sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by
    rintro _ n rfl; exact gram_pos hs n
  exact key _ _ h2

def oTop {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) :
    ∀ n, n = (I.rec7 l Z).R.m → OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)) :=
  fun n h => Eq.rec (motive := fun n _ => OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)))
    (topDec (gram_X hI _) (gram_X' hI)) h.symm

def piE (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : (I.rec7 l Z).host.E :=
  ((X.piT u : 𝓞 B.host.E) : B.host.E)

def zeta (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : Fin (lineZ (I.rec7 l Z)).rank → (I.rec7 l Z).host.E :=
  fun _ => piE I l Z u

def xgeo {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok)
    (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (u : B.Word)
    (Λ : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : XGeo (I.rec7 l Z) :=
  ⟨fun _ => stdSp _, vac, lineZ _, oTop l Z hI, zeta I l Z u, 1, Λ⟩

theorem norm_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    star (zeta I l Z u) ⬝ᵥ (lineZ (I.rec7 l Z)).gram *ᵥ zeta I l Z u = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) := by
  have h := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (l.pr.piT_norm u)
  rw [gram_pos, Matrix.one_mulVec]
  simp only [dotProduct, zeta, piE, Pi.star_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_mul, map_natCast] at h
  rw [show (lineZ (I.rec7 l Z)).rank = 1 from rfl, one_smul]
  exact (mul_comm _ _).trans h

theorem isLineVec_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    IsLineVec (lineZ (I.rec7 l Z)) (zeta I l Z u) := by
  refine ⟨rfl, ?_⟩
  rw [norm_zeta]
  have := (l.pr.T_prime u).ne_zero
  exact_mod_cast this

theorem eq_latFrame_of_isSDFrame {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.PlaceModel.latFrame V := by
  obtain ⟨c, -, -, -, h4, h5⟩ := h
  ext x
  constructor
  · intro hx
    have := h5 x hx
    rw [one_pow, Nat.cast_one, one_smul] at this
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame]
    exact this
  · intro hx
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame] at hx
    have := h4 x hx
    rwa [one_pow, Nat.cast_one, one_smul] at this

end GlobalTheory.XGeoStd
