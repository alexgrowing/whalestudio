import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.L2.SG.AutoReg

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}

def IntegrableDS (M : DSModel V S) : Prop :=
  ∀ τ, ∃ w : M.H τ, w ≠ 0 ∧ Integrable (Formalism.MainNotions.S.coefOn (ε := M.ε τ) (M.σ τ) w w) (Formalism.REAL.muG (M.ε τ))

open Classical in

structure IsL2Embedding (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (J : Set (GA D V))
    (χ : GA D V → ℂ) (Ψ : M.Vec → GA D V → ℂ) : Prop where
  meas : ∀ v, AEStronglyMeasurable (Ψ v) μ
  inv : ∀ v, ∀ γ ∈ GQ V, ∀ x, Ψ v (γ * x) = Ψ v x
  add : ∀ (v : M.Vec) τ (a b : M.sm τ), Ψ (Function.update v τ (a + b)) =ᵐ[μ]
    fun x => Ψ (Function.update v τ a) x + Ψ (Function.update v τ b) x
  smul : ∀ (v : M.Vec) τ (c : ℂ) (a : M.sm τ), Ψ (Function.update v τ (c • a)) =ᵐ[μ]
    fun x => c * Ψ (Function.update v τ a) x
  bdd : ∃ C : ℝ, ∀ v, ∫⁻ x in 𝓕, ‖Ψ v x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ∏ τ, ‖(v τ : M.H τ)‖ ^ 2)
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
    Ψ (Function.update v τ w) =ᵐ[μ] fun x => Ψ v (x * atTau θ V τ g)
  lev : ∀ (v : M.Vec), ∀ k ∈ J, (fun x => Ψ v (x * k)) =ᵐ[μ] fun x => χ k * Ψ v x

def L2AutomorphicRegular : Prop :=
  ∀ (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (J : Set (GA D V)) (χ : GA D V → ℂ),
    IsInfFam θ → V.SigOK → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IntegrableDS M →
    (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1) →
    ∀ Ψ, IsL2Embedding θ M μ 𝓕 J χ Ψ →
      ∃ T : MMap M, (∀ v, IsAutFunSm θ V (T v)) ∧ (∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g) ∧
        Formalism.IndefR.AutomorphicEvaluation.EqCont θ M T ∧ ∀ v, Ψ v =ᵐ[μ] T v

def L2Cuspidal : Prop :=
  ∀ (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (J : Set (GA D V)) (χ : GA D V → ℂ),
    IsInfFam θ → V.SigOK → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IntegrableDS M →
    (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1) →
    ∀ Ψ, IsL2Embedding θ M μ 𝓕 J χ Ψ → ∀ T : MMap M, (∀ v, IsAutFunSm θ V (T v)) →
      (∀ v, Ψ v =ᵐ[μ] T v) → ∀ v, IsCuspFun V (T v)

end Formalism.L2.SG.AutoReg

end
