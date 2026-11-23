import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open Ad3.LR Filter Topology

namespace GlobalTheory.CompanionTheory.RowPolarization

def HD (f : M22 → ℂ) (h e : M22) (d : ℂ) : Prop :=
  ∃ L : M22 →L[ℝ] ℂ, HasFDerivAt f L h ∧ L e = d

variable {f g : M22 → ℂ} {h e : M22} {d d' : ℂ}

def Dl (x : M22) : ℂ := (x 0 0 : ℂ) * (x 1 1 : ℂ) - (x 0 1 : ℂ) * (x 1 0 : ℂ)

def Ac (x : M22) : ℂ := (x 0 0 : ℂ) + (x 1 0 : ℂ) * Complex.I

def Bc (x : M22) : ℂ := (x 0 1 : ℂ) + (x 1 1 : ℂ) * Complex.I

def Gc (x : M22) : ℂ := (Ac x)⁻¹

def Tc : ℂ := 2 * Real.pi * Complex.I

def Fk (p : ℕ) (x : M22) : ℂ :=
  Dl x ^ (p + 1) * Gc x ^ (2 * p + 2 + 1) * Complex.exp (Tc * (Bc x * Gc x))

def Xc (p : ℕ) (x : M22) : ℂ :=
  (-(2 * (p : ℂ) + 3)) * Gc x * (x 0 0 : ℂ) + Tc * (Gc x * (x 0 1 : ℂ) - Bc x * (Gc x * Gc x) * (x 0 0 : ℂ))

def Yc (p : ℕ) (x : M22) : ℂ :=
  (-(2 * (p : ℂ) + 3)) * Gc x * (x 1 0 : ℂ) + Tc * (Gc x * (x 1 1 : ℂ) - Bc x * (Gc x * Gc x) * (x 1 0 : ℂ))

end GlobalTheory.CompanionTheory.RowPolarization
