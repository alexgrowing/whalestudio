import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

def IsSkew (μ : D.host.E) : Prop := μ ≠ 0 ∧ star μ = -μ

def Tm (A : HSp D) (μ : D.host.E) : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) D.host.E :=
  (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm

def IsChart (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) : Prop :=
  ∀ g, (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat (κ g) = mt (dblSp A) g * rat (Tm A μ)

def IntA (z : AE D) : Prop := ∀ v, compFin D.host.F D.host.E v z ∈ intLoc D.host.F D.host.E v

def IntGL {n : ℕ} (M : GL (Fin n) (AE D)) : Prop := (∀ i j, IntA (M.1 i j)) ∧ ∀ i j, IntA ((M⁻¹).1 i j)

def ScalData (μ : D.host.E) (u ε : (AE D)ˣ) : Prop :=
  (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) ∧
    ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4

def HalfData (t : AE D) : Prop := t + cA D t = 1 ∧ IntA t ∧ ∀ w, compInf D.host.F D.host.E w (2 * t) = 1

def IsConj (A : HSp D) (a : GL (Fin A.rank) (AE D)) (κ : GA D (dblSp A) ≃* G D A.rank) (p : siegel A) : Prop :=
  ∀ k : GA D (dblSp A), k ∈ Khat A a ↔ κ ((p : GA D (dblSp A))⁻¹ * k * p) ∈ K D A.rank

def hgtStd (A : HSp D) (a : GL (Fin A.rank) (AE D)) (κ : GA D (dblSp A) ≃* G D A.rank) (p : siegel A) :
    G D A.rank → ℝ≥0 := fun g => hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) * absA D (aP A p)

def IsTransport (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (κ : GA D (dblSp A) ≃* G D A.rank)
    (ω : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) : Prop :=
  ∀ g f, IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 f →
    (ω (κ g) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f)

def shift (ψ : AddChar (AF D.host.F) ℂ) (l : D.host.F) : AddChar (AF D.host.F) ℂ :=
  ψ.mulShift (algebraMap D.host.F (AF D.host.F) l)

def stdInv (n : ℕ) (μ : D.host.E) (τ : D.what₂.Tau) : Matrix (Fin (n + n)) (Fin (n + n)) ℂ :=
  (tauE D τ μ / (‖tauE D τ μ‖ : ℂ)) • blk4 0 1 (-1) 0

def IsStdInv (A : HSp D) (μ : D.host.E)
    (s : D.what₂.Tau → Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ) : Prop :=
  ∀ τ, s τ * (Tm A μ).map (tauE D τ) = (Tm A μ).map (tauE D τ) * stdInv A.rank μ τ

variable (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

def linF (τ : D.what₂.Tau) (X z : Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  ((4 * Real.pi * |l τ| * (Matrix.trace (Xᴴ * (gramAt D V τ * s τ) * z)).re : ℝ) : ℂ)

def annS (θ : InfFam D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) (φ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => deriv (fun t : ℝ => φ (x + lineAt θ τ X t)) 0 + linF V l s τ X (compAt θ τ x) * φ x

open Classical in

def annC (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ) :
    (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ :=
  fun z => deriv (fun t : ℝ => f (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) 0 + linF V l s τ X (Matrix.of (z τ)) * f z

end GlobalTheory.StdUnn

end
