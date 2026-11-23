import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PoissonAbs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

variable {D : D7} {n : ℕ}

def IsNMap (nb : hermA D n → G D n) : Prop := ∀ b, mat (nb b) = blk4 1 b.1 0 1

def fc (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (f : G D n → ℂ) (β : HermE D n) (g : G D n) : ℂ :=
  ∫ b in 𝓖, f (nb b * g) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam

def eis {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (Φ : schwartzA θ V.rank n) (g : G D n) : ℂ → ℂ :=
  fun z => GlobalTheory.Eis.cosetSum (P D n) (GF D n) (sect ω H Φ z) g

def lc {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (Φ : schwartzA θ V.rank n) (k : ℤ) : G D n → ℂ :=
  fun g => laurent (eis ω H Φ g) (s0 V n) k

structure Std (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) : Prop where
  hψ : IsCharAF D.host.F ψ
  hχ : IsHeckeChar D χ
  hη : ResEta D χ V.rank
  hθ : IsInfFam θ
  hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕
  hω : IsWeilSch ψ χ θ V μ ω
  hH : IsHeight H
  hl : HasRealPar ψ θ l
  hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)
  hν : ν.IsHaarMeasure
  hΦ : Φ.1 ∈ fockA θ V n l s

def InRange (V : HSp D) (n : ℕ) : Prop :=
  n < V.rank ∧ V.rank ≤ 2 * n ∧ n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank

def CoefData (nb : hermA D n → G D n) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) : Prop :=
  IsNMap nb ∧ IsCovolOneH lam 𝓖

def PoleOne : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    ∀ g, PoleLE (eis ω H Φ g) (s0 V n) 1

def LcAuto : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    ∀ k : ℤ, -1 ≤ k → k ≤ 0 → Continuous (lc ω H Φ k) ∧ LeftInv (GF D n) (lc ω H Φ k)

def LcCoef : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ (β : HermE D n) (g : G D n) (k : ℤ), -1 ≤ k → k ≤ 0 →
    CoeffAt (fun z => fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g) (s0 V n) k (fc ψ lam 𝓖 nb (lc ω H Φ k) β g)

def ThetaAuto : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    Continuous (thetaInt ω ν Φ) ∧ LeftInv (GF D n) (thetaInt ω ν Φ)

def CoefND : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g : G D n,
    HolValueAt (fun z => fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g) (s0 V n) (fc ψ lam 𝓖 nb (thetaInt ω ν Φ) β g)

def Unfold : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
  ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ (z : ℂ), (n : ℝ) / 2 < z.re → ∀ g : G D n,
    Integrable (fun b : hermA D n => sect ω H Φ z (w * nb b * g)) lam ∧
    fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g =
      ∫ b, sect ω H Φ z (w * nb b * g) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam

def ThetaCoef : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g : G D n,
    fc ψ lam 𝓖 nb (thetaInt ω ν Φ) β g = IfrB V ν (fun x => (ω g Φ).1 x) β

def VanishPole : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 →
    (∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g, fc ψ lam 𝓖 nb (lc ω H Φ (-1)) β g = 0) →
    ∀ g, lc ω H Φ (-1) g = 0

def VanishVal : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → (∀ g, lc ω H Φ (-1) g = 0) →
    (∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g, fc ψ lam 𝓖 nb (lc ω H Φ 0) β g = fc ψ lam 𝓖 nb (thetaInt ω ν Φ) β g) →
    ∀ g, lc ω H Φ 0 g = thetaInt ω ν Φ g

def FourierZero : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ f : G D n → ℂ, Continuous f → LeftInv (GF D n) f →
    (∀ β g, fc ψ lam 𝓖 nb f β g = 0) → f = 0

def CoefDataExists : Prop :=
  ∀ (D : D7) (n : ℕ), ∃ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖

end PositivityTheory.PfSWUS

end
