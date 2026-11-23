import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

def LabelsChar (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (θ : Tor p d →* ℂˣ) (x : Fbar p) : Prop :=
  x ^ (p ^ d - 1) = 1 ∧ ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)

def LabelsTame (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ) : Prop :=
  ∀ u : (ZMod p)ˣ, GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod p) (Fbar p) (a : ZMod p))
    (algebraMap (ZMod p) (Fbar p) (u : ZMod p)) = ((χ u : ℂˣ) : ℂ)

def rootElt {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (y : Σ c : Cyc b, Fin (cycLen b c)) : Fbar p :=
  x y.1 ^ p ^ (y.2 : ℕ)

def IsRootPoly {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, x c ^ (p ^ cycLen b c - 1) = 1) ∧ f.Monic ∧ Formalism.CyclotomicNorms.rootsBar f = Finset.univ.val.map (rootElt x)

def Labels (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, LabelsChar L (s.2 c) (x c)) ∧ IsRootPoly x f

def cuspOn {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) :
    GlobalTheory.GLq.Gn p (Fintype.card ι) → ℂ := fun y =>
  cuspChar θ ((y : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (ZMod p)).submatrix
    (Fintype.equivFin ι) (Fintype.equivFin ι))

end GlobalTheory.ParamLabel

end
