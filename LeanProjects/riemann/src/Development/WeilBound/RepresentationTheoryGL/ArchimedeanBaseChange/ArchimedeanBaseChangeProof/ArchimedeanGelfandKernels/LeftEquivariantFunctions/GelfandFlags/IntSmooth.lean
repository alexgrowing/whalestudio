import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def NInv {V : Type} (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (f : Mat n → V) : Prop :=
  ∀ u ∈ nilSet W₁ W₂, ∀ x ∈ GLs n, f (u.val * x) = f x

def QInv {X : Type} (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (A : Mat n → X) : Prop :=
  ∀ q ∈ GLs n, W₁.map (Matrix.mulVecLin q) = W₁ → W₂.map (Matrix.mulVecLin q) = W₂ → ∀ x ∈ GLs n, A (q * x) = A x

def IsField (E : KMod n) (A : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  ContDiffOn ℝ ∞ A (GLs n) ∧ ∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, A (x * k.1) = E.ρ k⁻¹ * A x * E.ρ k

def IntSmooth : Prop :=
  ∀ (n : ℕ) (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (F : X → Mat n → V), (∀ t, ContDiffOn ℝ ∞ (F t) (GLs n)) →
    (∀ m : ℕ, ContinuousOn (fun p : X × Mat n => iteratedFDeriv ℝ m (F p.1) p.2) (Set.univ ×ˢ GLs n)) →
    (∀ x₀ ∈ GLs n, ∃ U ∈ nhds x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U, F t x = 0) →
    ContDiffOn ℝ ∞ (fun x => ∫ t, F t x ∂ν) (GLs n)

def NAvg : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (E : KMod n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
    ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure] (φ : Mat n → E.V),
      φ ∈ CE E → (∃ R, ∀ y ∈ GLs n, R < lg y → φ y = 0) →
        (fun x => ∫ u : N, φ ((u : G n).val * x) ∂ν) ∈ CE E ∧ NInv W₁ W₂ (fun x => ∫ u : N, φ ((u : G n).val * x) ∂ν)

def WaveN : Prop :=
  WaveEx → WaveSpeed → GelComm → ∀ (n : ℕ) (E : KMod n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (f : Mat n → E.V), f ∈ CE E →
    NInv W₁ W₂ f → ∃ u, IsWave E u ∧ (∀ g ∈ GLs n, u 0 g = f g) ∧ ∀ t, NInv W₁ W₂ (u t)

def WaveA : Prop :=
  GelFlag → ∀ (n : ℕ) (E : KMod n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → ∀ (A : Mat n → (E.V →L[ℂ] E.V))
    (u : ℝ → Mat n → E.V), IsField E A → QInv W₁ W₂ A → IsWave E u → (∀ t, NInv W₁ W₂ (u t)) →
      IsWave E (fun t x => A x (u t x))

def KerComm : Prop :=
  WaveEx → WaveSpeed → GelComm → GelFlag → IntSmooth →
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E w g k →
    ∀ (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → ∀ (A : Mat n → (E.V →L[ℂ] E.V)), IsField E A → QInv W₁ W₂ A →
      ∀ f ∈ CE E, NInv W₁ W₂ f → ∀ x ∈ GLs n, act μ E k (fun y => A y (f y)) x = A x (act μ E k f x)

def KerNId : Prop :=
  NilUni → KerZero → NAvg →
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ →
    ∀ (ν : Measure N) [ν.IsHaarMeasure] (A : Mat n → (E.V →L[ℂ] E.V)), IsField E A → QInv W₁ W₂ A →
    (∀ f ∈ CE E, NInv W₁ W₂ f → ∀ x ∈ GLs n, act μ E k (fun y => A y (f y)) x = A x (act μ E k f x)) →
    ∀ y ∈ GLs n, (∫ u : N, k ((u : G n).val * y) ∂ν) * A y = A 1 * ∫ u : N, k ((u : G n).val * y) ∂ν

def LgCpt : Prop := ∀ (n : ℕ) (R : ℝ), IsCompact {y : G n | lg y.val ≤ R}

def TrZero : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B T e i : V →L[ℂ] V) (c : ℂ), c ≠ 0 →
    e * i + i * e = c • 1 → e * B = -(B * e) → T * e = e * T →
      LinearMap.trace ℂ V ((B * T : V →L[ℂ] V) : V →ₗ[ℂ] V) = 0

def VCKer : Prop :=
  WaveEx → WaveSpeed → GelComm → GelFlag → FlagField → NilUni → KerZero → IntSmooth →
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (w : List (Bool × ℕ)) (g : ℝ → ℝ)
      (τ : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g τ → IsKer μ E w g k →
      ∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
        (fun v => d.val *ᵥ v) '' perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' perp W₁ = W₂ →
        ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
          Integrable (fun u : N => phiOf E T k (u * d)) ν ∧ ∫ u : N, phiOf E T k (u * d) ∂ν = 0

end PositivityTheory.RgBcC.VC
