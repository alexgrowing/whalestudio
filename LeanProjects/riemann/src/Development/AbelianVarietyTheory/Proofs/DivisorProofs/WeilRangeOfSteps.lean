import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWWeil

open GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

abbrev unipN (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) : Subgroup (UA σ J₂) :=
  unipOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype

abbrev ratN (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) : Subgroup (unipN σ J₂) :=
  (ratU σ J₂).comap (unipN σ J₂).subtype

def IsRatChar {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (lam : unipN σ J₂ →* Circle) : Prop :=
  Continuous (fun x => (lam x : ℂ)) ∧ ∀ x ∈ ratN σ J₂, lam x = 1

def coefN {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂))
    (lam : unipN σ J₂ →* Circle) (A : UA σ J₂ → ℂ) (g : UA σ J₂) : ℂ :=
  ⨍ x in 𝓓, A ((x : UA σ J₂) * g) * (starRingEnd ℂ) (lam x : ℂ) ∂νN

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type}

def eisW (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : ℂ :=
  GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂) (fun x => om (1, x) Φ 0) g

def thetaI [Fintype κ] (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) (ν : Measure (UA σ JV))
    (𝓕 : Set (UA σ JV)) (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : ℂ :=
  ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν

end GlobalTheory.SWWeil

namespace GlobalTheory.SWWeil
open GlobalTheory.SWLit GlobalTheory.SWACase

def StepConv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
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
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) (eisW σ om Φ g)

def StepReg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
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
  (∀ g, Continuous fun x : unipN σ J₂ => eisW σ om Φ ((x : UA σ J₂) * g) - thetaI σ om ν 𝓕 Φ ((x : UA σ J₂) * g)) ∧
  ∀ x ∈ ratN σ J₂, ∀ g, eisW σ om Φ ((x : UA σ J₂) * g) - thetaI σ om ν 𝓕 Φ ((x : UA σ J₂) * g) =
    eisW σ om Φ g - thetaI σ om ν 𝓕 Φ g

def StepCoef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
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
  ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam →
  ∀ g, coefN σ νN 𝓓 lam (fun x => eisW σ om Φ x - thetaI σ om ν 𝓕 Φ x) g = 0

def StepUniq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (n : ℕ), 1 ≤ n →
  ∀ (l : E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∃ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure ∧ IsFundamentalDomain (ratN σ J₂) 𝓓 νN ∧
    ∀ A : UA σ J₂ → ℂ, (∀ g, Continuous fun x : unipN σ J₂ => A ((x : UA σ J₂) * g)) →
      (∀ x ∈ ratN σ J₂, ∀ g, A ((x : UA σ J₂) * g) = A g) →
      (∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam → ∀ g, coefN σ νN 𝓓 lam A g = 0) → ∀ g, A g = 0

end GlobalTheory.SWWeil
