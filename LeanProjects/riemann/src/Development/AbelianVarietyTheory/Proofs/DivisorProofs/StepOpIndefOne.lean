import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MidRangeOfOn

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWOpCase

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF

def DefinitePlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ), 3 ≤ m → ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    ∃ ι : F →+* ℝ, Formalism.UG.IsDefiniteAt σ (l • JV) ι

def StepOpDefinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    ∀ ι : F →+* ℝ, Formalism.UG.IsDefiniteAt σ (l • JV) ι →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ Φ ∈ kfin σ om K,
  ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ W ≤ kfin σ om K ∧
  ∃ Φ' ∈ W, sec σ om Φ' = sec σ om Φ ∧ thetaI σ om ν 𝓕 Φ' = thetaI σ om ν 𝓕 Φ ∧
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ρ : Measure Ω) (y : Ω → UA σ J₂) (η : Ω → ℂ) (C : Set (UA σ J₂)),
    IsFiniteMeasure ρ ∧ Measurable y ∧ IsCompact C ∧ (∀ ω, y ω ∈ C) ∧ Integrable η ρ ∧
    (∀ D : UA σ J₂ → ℂ, Continuous D → (∀ γ ∈ ratU σ J₂, ∀ g, D (γ * g) = D g) → IsSing σ T D →
      ∀ g, ∫ ω, η ω * D (g * y ω) ∂ρ = 0) ∧
    ∃ L : ℂ → W →ₗ[ℂ] W, (∀ (Ψ : W) (f : Module.Dual ℂ W), Differentiable ℂ fun s => f (L s Ψ)) ∧
      Function.Bijective (L (((m : ℂ) - (n : ℂ)) / 2)) ∧
      (∀ (Ψ : W) (s : ℂ) (g : UA σ J₂), ∫ ω, η ω * flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om (Ψ : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s (g * y ω) ∂ρ =
        flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om ((L s Ψ : W) : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s g) ∧
      ∀ (Ψ : W) (g : UA σ J₂), ∫ ω, η ω * thetaI σ om ν 𝓕 (Ψ : (κ → AF F) → ℂ) (g * y ω) ∂ρ =
        thetaI σ om ν 𝓕 ((L (((m : ℂ) - (n : ℂ)) / 2) Ψ : W) : (κ → AF F) → ℂ) g

def StepOpIndefOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    n = 1 → (∀ ι : F →+* ℝ, ¬ Formalism.UG.IsDefiniteAt σ (l • JV) ι) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ Φ ∈ kfin σ om K,
  ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ W ≤ kfin σ om K ∧
  ∃ Φ' ∈ W, sec σ om Φ' = sec σ om Φ ∧ thetaI σ om ν 𝓕 Φ' = thetaI σ om ν 𝓕 Φ ∧
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ρ : Measure Ω) (y : Ω → UA σ J₂) (η : Ω → ℂ) (C : Set (UA σ J₂)),
    IsFiniteMeasure ρ ∧ Measurable y ∧ IsCompact C ∧ (∀ ω, y ω ∈ C) ∧ Integrable η ρ ∧
    (∀ D : UA σ J₂ → ℂ, Continuous D → (∀ γ ∈ ratU σ J₂, ∀ g, D (γ * g) = D g) → IsSing σ T D →
      ∀ g, ∫ ω, η ω * D (g * y ω) ∂ρ = 0) ∧
    ∃ L : ℂ → W →ₗ[ℂ] W, (∀ (Ψ : W) (f : Module.Dual ℂ W), Differentiable ℂ fun s => f (L s Ψ)) ∧
      Function.Bijective (L (((m : ℂ) - (n : ℂ)) / 2)) ∧
      (∀ (Ψ : W) (s : ℂ) (g : UA σ J₂), ∫ ω, η ω * flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om (Ψ : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s (g * y ω) ∂ρ =
        flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om ((L s Ψ : W) : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s g) ∧
      ∀ (Ψ : W) (g : UA σ J₂), ∫ ω, η ω * thetaI σ om ν 𝓕 (Ψ : (κ → AF F) → ℂ) (g * y ω) ∂ρ =
        thetaI σ om ν 𝓕 ((L (((m : ℂ) - (n : ℂ)) / 2) Ψ : W) : (κ → AF F) → ℂ) g

end GlobalTheory.SWOpCase

end
