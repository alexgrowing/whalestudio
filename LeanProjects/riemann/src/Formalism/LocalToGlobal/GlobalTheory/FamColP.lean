import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.GlobalTheory.FamRecP
import Formalism.LocalToGlobal.GlobalTheory.ArithP
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SecondPriceSumWeightsUncovered
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AnalyticFirstToLatticeDiscriminant

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamCol

open Formalism Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.DIV

section One

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

variable {C : ColObj K I} {P : PlDat K I}

variable [IsTotallyComplex K] {m : ℕ} (R : RowArg C)

end One

section Two

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {I : Type} {m : ℕ}
  (C : ColIface K I) {P : PlDat K I} (R : RowArg C.toColObj)

theorem ColFacts.elim {C : ColObj K I} (h : ColFacts C) {p : ColObj K I → Prop}
    (hp : ∀ J : ColIface K I, p J.toColObj) : p C := by
  obtain ⟨J, rfl⟩ := h
  exact hp J

end Two

section Three

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {P : PlDat K I}

end Three

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem Pt.du_pos {I : Type} (Q : Pt I) (h : ColFacts Q.C) (m : ℕ) (u : I) : 0 < (Q.fam m).du u := by
  show (0 : ℝ) < (Fintype.card (Q.C.M u).ι : ℝ)
  exact_mod_cast h.elim (p := fun C => 0 < Fintype.card (C.M u).ι) (fun J => J.rank_pos u)

theorem SameNumbers.symm {I : Type} [Fintype I] {m : ℕ} {F F' : Fam I m} (h : SameNumbers F F') : SameNumbers F' F where
  du u := (h.du u).symm
  dM u := (h.dM u).symm
  T u := (h.T u).symm
  muN u := (h.muN u).symm
  muMaxN u := (h.muMaxN u).symm
  h u := (h.h u).symm
  muM u := (h.muM u).symm
  muMaxM u := (h.muMaxM u).symm
  EeJ u j := (h.EeJ u j).symm
  muCC := h.muCC.symm
  muMinCC := h.muMinCC.symm
  Fo := h.Fo.symm
  Ga := h.Ga.symm
  Ta := h.Ta.symm
  IO := h.IO.symm
  del := h.del.symm
  e0 := h.e0.symm

end Family

section Rec

end Rec

section FamPt

open Formalism.MainNotions

variable {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x) {Del h0 : ℕ}

@[reducible] def plOfFam (Lv : Arith.Lev (Arith.datumOf (Fm.D x i) (Fm.L x i) Del h0)) (sd : (Fm.D x i).what₂.LL) :
    PlDat (Fm.D x i).what₂.LL (Fm.D x i).what₂.Word :=
  ⟨Arith.datumOf (Fm.D x i) (Fm.L x i) Del h0, Arith.cstOf Fm, Lv, sd, fun u => (Fm.D x i).s.letter u⟩

variable {Lv : Arith.Lev (Arith.datumOf (Fm.D x i) (Fm.L x i) Del h0)} {sd : (Fm.D x i).what₂.LL}

end FamPt

section Tied

open Formalism.MainNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

end Tied

section Conc

end Conc

section Dat

end Dat

section ConcNum

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

namespace GlobTied

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {num : ScNum} {G : Glob} {TT : Finset H}
  {a : H → ℝ} {w : Fin R.m → E0 × H → ℝ} (T : GlobTied W num G TT a w)

include T

theorem f_eq : X.f = (PhiSet (H := H)).card := by
  unfold Fields.f
  rw [Fintype.card_congr T.σ, Fintype.card_coe]

end GlobTied

end ConcNum

end Formalism.L2.GlobalTheoryTheory.FamCol

end
