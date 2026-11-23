import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

def blk4 {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def blkA {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

variable (D : D7) (n : ℕ)

def Jst : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E := blk4 0 1 (-1) 0

abbrev G : Type := GAd D.sp.cm.sig (Jst D n)

abbrev GF : Subgroup (G D n) := AdelicU.ratPts D.sp.cm.sig (Jst D n)

variable {D n} in

def mat (g : G D n) : Mx D (n + n) (n + n) := (AdelicU.matHom _ D.sp.cm.sig (Jst D n) g).1

def upperHalf : Submodule (AE D) (Fin (n + n) → AE D) :=
  LinearMap.ker (LinearMap.funLeft (AE D) (AE D) fun i : Fin n => finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n))

def P : Subgroup (G D n) := (Formalism.UG.stabGL (upperHalf D n)).comap (AdelicU.matHom _ D.sp.cm.sig (Jst D n))

def K : Subgroup (G D n) := levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1

variable {D n}

def IsHeight (H : G D n → ℝ≥0) : Prop :=
  ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ k ∈ K D n,
    H (p * k) = absA D (Matrix.GeneralLinearGroup.det a)

abbrev trA (z : AE D) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) z

def halfTr (z : AE D) : AF D.host.F := algebraMap D.host.F (AF D.host.F) (1 / 2) * trA z

def inner (V : HSp D) (x y : Mx D V.rank n) : Mx D n n := adj x ⬝ (gA V ⬝ y)

structure IsWeilSch (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (V : HSp D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) : Prop where

  levi : ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ Φ x,
    (ω g Φ).1 x = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) * Φ.1 (x ⬝ a.1)

  unip : ∀ (g : G D n) (b : Mx D n n), mat g = blk4 1 b 0 1 → ∀ Φ x,
    (ω g Φ).1 x = ψ (halfTr (Matrix.trace (b ⬝ inner V x x : Mx D n n))) * Φ.1 x

  weyl : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → ∀ Φ x,
    (ω g Φ).1 x = ∫ y, Φ.1 y * ψ (trA (Matrix.trace (inner V x y))) ∂μ

def HasRealPar (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ) : Prop :=
  ∀ x : Ainf D.host.F, psiInf D.host.F ψ x =
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (l τ : ℂ) * θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)))

def gauss (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ∑ τ, ((|l τ| : ℝ) : ℂ) * Matrix.trace ((z τ)ᴴ * (gramAt D V τ * s τ) * z τ))

def evalPoly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun k => if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) p

def fockA (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Submodule ℂ (Mx D V.rank n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
        g (fun i j => finPart D (x i j))}

variable {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))

def s0 (V : HSp D) (n : ℕ) : ℂ := (V.rank : ℂ) / 2 - (n : ℂ) / 2

def sect (H : G D n → ℝ≥0) (Φ : schwartzA θ V.rank n) (s : ℂ) (g : G D n) : ℂ :=
  npow (H g) (s - s0 V n) * (ω g Φ).1 0

def theta (Φ : schwartzA θ V.rank n) (g : G D n) (h : GA D V) : ℂ :=
  ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (mt V h⁻¹ ⬝ (rat ξ : Mx D V.rank n))

def thetaInt (ν : Measure (GA D V)) (Φ : schwartzA θ V.rank n) (g : G D n) : ℂ :=
  ⨍ q, AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q ∂autMeasure V ν

end GlobalTheory.StdUnn

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def SiegelWeilUnitarySchrodinger : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ H : G D n → ℝ≥0, IsHeight H →
  ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
  ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν)) ∧
    (∀ z : ℂ, (n : ℝ) / 2 < z.re → LeftInv (P D n ⊓ GF D n) (sect ω H Φ z) ∧
      ∀ g, Eis.CosetConv (P D n) (GF D n) (sect ω H Φ z) g) ∧
    ∀ g, HolValueAt (fun z => Eis.cosetSum (P D n) (GF D n) (sect ω H Φ z) g) (s0 V n) (thetaInt ω ν Φ g)

end GlobalTheory.Published

end
