import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def nbar (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks 1 0 c 1

def mM (a : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks a 0 0 (aᴴ)⁻¹

def IsSch {m : ℕ} (f : (Fin m → Fin n → ℂ) → ℂ) : Prop := ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑S = f

def AwayCls {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (Ψ : Mx D m n → ℂ) : Prop :=
  (∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) →
    Ψ x = Ψ x') ∧ ∀ f, IsSch f → tens θ τ fr f Ψ ∈ schwartzA θ m n

def Decomp : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ y₁ y₂ y₃ y₄ : GR n, y = y₁ * y₂ * y₃ * y₄ ∧
    (∃ t : ℝ, mR y₁ = nU ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) ∧ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y₂ = nbar c) ∧
    (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y₃ = mM a) ∧ (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y₄ = nU b)

def LNe : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def AwayIn : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → (∀ τ', l τ' ≠ 0) → ∀ Ψ ∈ awayA θ V n l s τ,
      AwayCls θ τ fr Ψ

def SchFP : Prop := ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, IsSch (fP c P)

def OpGen : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ

end PositivityTheory.Rg.Sw.Glob
