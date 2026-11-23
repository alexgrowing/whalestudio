import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def colMat {n : ℕ} (w : Fin n → Fin n → EAf D) : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => w j i

def pairAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (bwdT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (fun i => bwT X h (Fin.rev i)) (z0T X h)

def hY (D : D7) (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  Formalism.UG.hform (GlobalTheory.StdFrames.sg D) (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) x y

def SmallAt (PP : Pl D.host.E) (x : EAf D) : Prop := Valued.v (GlobalTheory.StdFrames.cpt PP x) < 1

def PairTable {M A : Type} [Ring A] (p : M → M → A) (sm : A → Prop) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M)
    (z : M) : Prop :=
  (∀ a c, sm (p (f a) (e c) - if a = c then 1 else 0)) ∧ (∀ a j, sm (p (f a) (b j))) ∧ (∀ a, sm (p (f a) z)) ∧
  (∀ a c, sm (p (f a) (f c))) ∧
  (∀ i a, sm (p (b' i) (e a))) ∧ (∀ i j, sm (p (b' i) (b j) - if i = j then 1 else 0)) ∧ (∀ i, sm (p (b' i) z)) ∧
  (∀ i a, sm (p (b' i) (f a))) ∧
  (∀ a, sm (p z (e a))) ∧ (∀ j, sm (p z (b j))) ∧ sm (p z z + 1) ∧ (∀ a, sm (p z (f a))) ∧
  (∀ a c, sm (p (e a) (e c))) ∧ (∀ a j, sm (p (e a) (b j))) ∧ (∀ a, sm (p (e a) z)) ∧
  (∀ a c, sm (p (e a) (f c) - if a = c then 1 else 0))

def sgnD {A : Type} [Ring A] (ρ k : ℕ) {n : ℕ} (a : Fin n) : A := if a.1 = ρ + k then -1 else 1

end GlobalTheory.SeeConjRead
