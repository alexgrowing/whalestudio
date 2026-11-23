import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

variable {D : D7} {n : ℕ}

def whitAt (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (β : HermE D n) (g : G D n) :
    ℂ → ℂ :=
  fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ φ b *
    ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam

def HeightKInv : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ x : G D n, ∀ k ∈ K D n, H (x * k) = H x

def FockKStable : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → ∀ k ∈ K D n, (ω k Φ).1 ∈ fockA θ V n l s

def WhitK : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ k ∈ K D n,
    HolValueAt (whitAt ψ V μ lam nb w H (ω k Φ).1 β k) (s0 V n) (IfrB V ν (ω k Φ).1 β)

def WhitOne : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ φ : Mx D V.rank n → ℂ, φ ∈ fockA θ V n l s →
    HolValueAt (whitAt ψ V μ lam nb w H φ β 1) (s0 V n) (IfrB V ν φ β)

def IwaRed : Prop := WhitK → WhitNDg

def WhitKOfOne : Prop := HeightKInv → FockKStable → WhitOne → WhitK

def IsPureFock (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : Mx D V.rank n → ℂ) : Prop :=
  ∃ (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (d : ℕ)
    (bs : Module.Basis (Fin d) D.host.F D.host.E)
    (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ),
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv ∧
    φ = fun x => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))

def WhitPure : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ φ : Mx D V.rank n → ℂ, IsPureFock θ V l s φ →
    HolValueAt (whitAt ψ V μ lam nb w H φ β 1) (s0 V n) (IfrB V ν φ β)

def WhitSpan : Prop := WhitPure → WhitOne

def ProdHol : Prop :=
  ∀ (ι : Type) [Countable ι] (f : ι → ℂ → ℂ) (U : Set ℂ), IsOpen U → (∀ i, AnalyticOnNhd ℂ (f i) U) →
    (∀ C ⊆ U, IsCompact C → ∃ c : ι → ℝ, Summable c ∧ ∀ i, ∀ z ∈ C, ‖f i z - 1‖ ≤ c i) →
    AnalyticOnNhd ℂ (fun z => ∏' i, f i z) U ∧ ∀ z ∈ U, Multipliable fun i => f i z

def WhitPureOfLocal : Prop :=
  Loc.LocFin → PositivityTheory.Rg.Sw.WR.WRSt → Loc.SiegelDensitiesLow → ProdHol → WhitPure

end PositivityTheory.PfSWUS

end
