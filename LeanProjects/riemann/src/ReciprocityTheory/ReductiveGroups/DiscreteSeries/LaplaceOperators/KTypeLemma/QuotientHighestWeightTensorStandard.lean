import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Tensor

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def prj (c : Fin n) : (Fin n → M) →ₗ[ℂ] M := LinearMap.proj (R := ℂ) (φ := fun _ : Fin n => M) c

def tensV (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => E a b ∘ₗ prj c + (if c = a then prj b else 0)

def tensVd (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => E a b ∘ₗ prj c - (if c = b then prj a else 0)

def eeV (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun d => ∑ c, E c d ∘ₗ prj c

def eeVd (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun d => -∑ c, E d c ∘ₗ prj c

def thV (lam : Fin n → ℝ) (s : Fin n) : ℝ := lam s - ((n : ℝ) - 1) / 2

def thVd (lam : Fin n → ℝ) (s : Fin n) : ℝ := -lam s - ((n : ℝ) - 1) / 2

def prodShift {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    Module.End ℂ X :=
  (List.ofFn fun t : Fin n => A - ((θ t : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod

def Xs (A : Module.End ℂ (Fin n → M)) (S : Submodule ℂ M) (θ : ℝ) : Submodule ℂ (Fin n → M) :=
  Submodule.pi Set.univ (fun _ => S) ⊓ LinearMap.ker (A - ((θ : ℝ) : ℂ) • (1 : Module.End ℂ (Fin n → M)))

end Tensor

def InRootCone (β : Fin n → ℝ) : Prop :=
  ∃ m : Fin n → Fin n → ℕ, β = ∑ a, ∑ b, if a < b then (m a b : ℝ) • root a b else 0

def TensStatement (n : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E →
    IsGlRep (tensV E) ∧ IsGlRep (tensVd E) ∧
    (∀ f : Fin n → M, casimir (tensV E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeV E f) ∧
    (∀ f : Fin n → M, casimir (tensVd E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeVd E f)

def VermaProductIdentity (n : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M),
    IsGlRep E → (∀ a b, b < a → E a b φ = 0) → (∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) →
    genSub E (Submodule.span ℂ {φ}) = ⊤ →
    prodShift (eeV E) (thV lam) = 0 ∧ prodShift (eeVd E) (thVd lam) = 0

def VermaConeStatement (n : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (s : Fin n),
    IsGlRep E → (∀ a b, b < a → E a b φ = 0) → (∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) →
    genSub E (Submodule.span ℂ {φ}) = ⊤ → StrictAnti lam →
    ((∀ (μ : Fin n → ℝ) (f : Fin n → M), f ∈ Xs (eeV E) ⊤ (thV lam s) → f ≠ 0 →
        (∀ a, tensV E a a f = ((μ a : ℝ) : ℂ) • f) → InRootCone (μ - (lam + rho n + Pi.single s 1))) ∧
      ∀ f₁ f₂ : Fin n → M, f₁ ∈ Xs (eeV E) ⊤ (thV lam s) → f₂ ∈ Xs (eeV E) ⊤ (thV lam s) →
        (∀ a, tensV E a a f₁ = (((lam + rho n + Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • f₁) →
        (∀ a, tensV E a a f₂ = (((lam + rho n + Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • f₂) →
        ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0) ∧
    ((∀ (μ : Fin n → ℝ) (f : Fin n → M), f ∈ Xs (eeVd E) ⊤ (thVd lam s) → f ≠ 0 →
        (∀ a, tensVd E a a f = ((μ a : ℝ) : ℂ) • f) → InRootCone (μ - (lam + rho n - Pi.single s 1))) ∧
      ∀ f₁ f₂ : Fin n → M, f₁ ∈ Xs (eeVd E) ⊤ (thVd lam s) → f₂ ∈ Xs (eeVd E) ⊤ (thVd lam s) →
        (∀ a, tensVd E a a f₁ = (((lam + rho n - Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • f₁) →
        (∀ a, tensVd E a a f₂ = (((lam + rho n - Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • f₂) →
        ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0)

def LowestKTypeEulerTensorStandard (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → prodShift (eeV E) (thV lam) f = 0

def EigenspaceWeightConeStandard (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (s : Fin n),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ (μ : Fin n → ℝ) (f : Fin n → D), f ∈ Xs (eeV E) (genSub E V) (thV lam s) → f ≠ 0 →
          IsKHWVec ε (tensV E) μ f → InRootCone (μ - lowK ε (lam + Pi.single s 1))) ∧
      ∀ f₁ f₂ : Fin n → D, f₁ ∈ Xs (eeV E) (genSub E V) (thV lam s) →
        f₂ ∈ Xs (eeV E) (genSub E V) (thV lam s) →
        IsKHWVec ε (tensV E) (lowK ε (lam + Pi.single s 1)) f₁ →
        IsKHWVec ε (tensV E) (lowK ε (lam + Pi.single s 1)) f₂ →
        ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0

def QuotientHighestWeightTensorStandard (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (s : Fin n)
    (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] (EN : Fin n → Fin n → Module.End ℂ N)
    (φ : (Fin n → D) →ₗ[ℂ] N) (x : Fin n → D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      StrictAnti (lam + Pi.single s 1) → IsGlRep EN → IsInfUnitary ε EN →
      (∀ (a b : Fin n) (f : Fin n → D), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f)) →
      x ∈ Xs (eeV E) (genSub E V) (thV lam s) → φ x ≠ 0 →
      ∃ W : Submodule ℂ N, W ≤ (Xs (eeV E) (genSub E V) (thV lam s)).map φ ∧
        IsKIrrHW ε EN (lowK ε (lam + Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir EN v = (casVal (lam + Pi.single s 1) : ℂ) • v

def LowestKTypeEulerTensorDual (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → prodShift (eeVd E) (thVd lam) f = 0

def EigenspaceWeightConeDual (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (s : Fin n),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ (μ : Fin n → ℝ) (f : Fin n → D), f ∈ Xs (eeVd E) (genSub E V) (thVd lam s) → f ≠ 0 →
          IsKHWVec ε (tensVd E) μ f → InRootCone (μ - lowK ε (lam - Pi.single s 1))) ∧
      ∀ f₁ f₂ : Fin n → D, f₁ ∈ Xs (eeVd E) (genSub E V) (thVd lam s) →
        f₂ ∈ Xs (eeVd E) (genSub E V) (thVd lam s) →
        IsKHWVec ε (tensVd E) (lowK ε (lam - Pi.single s 1)) f₁ →
        IsKHWVec ε (tensVd E) (lowK ε (lam - Pi.single s 1)) f₂ →
        ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0

def QuotientHighestWeightTensorDual (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (s : Fin n)
    (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] (EN : Fin n → Fin n → Module.End ℂ N)
    (φ : (Fin n → D) →ₗ[ℂ] N) (x : Fin n → D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapLap ε lam h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      StrictAnti (lam - Pi.single s 1) → IsGlRep EN → IsInfUnitary ε EN →
      (∀ (a b : Fin n) (f : Fin n → D), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f)) →
      x ∈ Xs (eeVd E) (genSub E V) (thVd lam s) → φ x ≠ 0 →
      ∃ W : Submodule ℂ N, W ≤ (Xs (eeVd E) (genSub E V) (thVd lam s)).map φ ∧
        IsKIrrHW ε EN (lowK ε (lam - Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir EN v = (casVal (lam - Pi.single s 1) : ℂ) • v

def HighestWeightCompactComparison (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapAtLeast ε lam h →
      max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
        (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ))) < h →
      1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ (μ : Fin n → ℝ) (w : D), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w → InRootCone (μ - lowK ε lam)) ∧
      ∀ w₁ w₂ : D, w₁ ∈ genSub E V → w₂ ∈ genSub E V →
        IsKHWVec ε E (lowK ε lam) w₁ → IsKHWVec ε E (lowK ε lam) w₂ →
        ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • w₁ + c₂ • w₂ = 0

def SchmidCasimirStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (ν : Fin n → ℝ) (h : ℝ) (c : ℂ)
    (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] (EN : Fin n → Fin n → Module.End ℂ N)
    (W : Submodule ℂ N),
    IsGlRep EN → IsInfUnitary ε EN → IsKIrrHW ε EN ν W →
    (∀ x ∈ Wm ε EN W, phi EN 1 x = 0) → (∀ v ∈ W, casimir EN v = c • v) →
    (∀ a, ∃ m : ℤ, (ν + rhoC ε - rhoN ε) a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →
    StrictAnti (ν + rhoC ε - rhoN ε) → GapAtLeast ε (ν + rhoC ε - rhoN ε) h → hNeed ε < h + 2 →
    1 ≤ pOf ε → 1 ≤ qOf ε →
    c = (casVal (ν + rhoC ε - rhoN ε) : ℂ)

def GenStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (V : Submodule ℂ M), IsGlRep E → IsKStableSub ε E V →
    (∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) →
      f ∈ genSub (tensV E) (Submodule.pi Set.univ fun _ => V)) ∧
    ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → f ∈ genSub (tensVd E) (Submodule.pi Set.univ fun _ => V)

def ConeNormStatement (n : ℕ) : Prop :=
  ∀ lam' β : Fin n → ℝ, Antitone lam' → InRootCone β → nsq (lam' + β) = nsq lam' → β = 0

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
