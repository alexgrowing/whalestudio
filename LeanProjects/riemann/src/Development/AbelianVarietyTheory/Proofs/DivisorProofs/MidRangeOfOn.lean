import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRangeOfSteps

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWMidF

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def IsSingChar (T : GL (Fin (n + n)) E) (lam : unipN σ J₂ →* Circle) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) E, a.det = 0 ∧ ∀ (x : unipN σ J₂) (b : Matrix (Fin n) (Fin n) (AE F E)),
    inBasis σ T (x : UA σ J₂) = blk 1 b 0 1 → (incM F (a.map σ))ᵀ * b * incM F a = 0 → lam x = 1

def IsSing (T : GL (Fin (n + n)) E) (D : UA σ J₂ → ℂ) : Prop :=
  ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam → ¬ IsSingChar σ T lam → ∀ g, coefN σ νN 𝓓 lam D g = 0

end Defs

def StepCoefOn (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n → R n m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∃ c : ℂ, ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam → ¬ IsSingChar σ T lam →
  ∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (fun s => coefN σ νN 𝓓 lam (fun x => eis σ om K Φ x s) g) (((m : ℂ) - (n : ℂ)) / 2)
    (c * coefN σ νN 𝓓 lam (thetaI σ om ν 𝓕 Φ) g)

def StepOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
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

def StepConstMid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ c : ℂ, (∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (eis σ om K Φ g) (((m : ℂ) - (n : ℂ)) / 2) (c * thetaI σ om ν 𝓕 Φ g)) → c = 1

def MidCOn (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n → R n m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∃ c : ℂ, ∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (eis σ om K Φ g) (((m : ℂ) - (n : ℂ)) / 2) (c * thetaI σ om ν 𝓕 Φ g)

def MidOn (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n → R n m →
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

end GlobalTheory.SWMidF

end
