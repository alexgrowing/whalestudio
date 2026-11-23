import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

open GlobalTheory.SWLit

def SiegelWeilAnisotropicWitt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

end GlobalTheory.Published

end
