import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CalcSteps : Prop :=
  AbsFC ∧ AbsCut ∧ Fcurve ∧ WvAlg ∧ ClsFacts ∧ SobOps ∧ CptSob ∧ SecBound ∧ PresSob ∧ ConcT ∧ CurveJoint ∧
    Friedrichs ∧ OmFormula ∧ IbpSob ∧ DenseD

def hg (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℂ := (cut c y : ℂ) * ∫ t, (g t : ℂ) * chj 0 t y

def PWdecay : Prop :=
  ∀ (c : ℝ) (g : ℝ → ℝ) (T : ℝ), IsBump g T →
    (∀ m : ℕ, Continuous (fun y : ℝ => (y : ℂ) ^ m * hg c g y) ∧
      Tendsto (fun y : ℝ => (y : ℂ) ^ m * hg c g y) (cocompact ℝ) (𝓝 0)) ∧
    ∀ N : ℕ, 1 ≤ N → ∫ t, (g t : ℂ) • toC0 (wv c N 0 t) = toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)

def SmoothOp : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      LgFacts → Unimod → RCalc → SobG → AlgEst → CalcSteps →
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ h : C₀(ℝ, ℂ), (∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y) →
      ∃ C : ℝ, ∀ x ∈ closure {x : Lp E.V 2 μ | ∃ f, Sob μ f ∧ IsSec E f ∧ cls μ f = x},
        ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h x ∧ ‖f' 1‖ ≤ C * ‖x‖

def KerCore : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ), IsBump g T → LgFacts → Unimod → RCalc → SobG → AlgEst → WaveSpeed → WaveCpt → CalcSteps →
    SmoothOp → PWdecay →
    ∃ k : Mat n → (E.V →L[ℂ] E.V), ContDiffOn ℝ ∞ k (GLs n) ∧ (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) ∧
      (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) ∧
      ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) →
        ∀ x ∈ GLs n, act μ E k f x = ∫ t, (g t : ℂ) • u t x

def KerLoc : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → LgFacts → Unimod → RCalc → WaveSpeed → WaveCpt →
    ContDiffOn ℝ ∞ k (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    (∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) →
      ∀ x ∈ GLs n, act μ E k f x = ∫ t, (g t : ℂ) • u t x) →
    IsKer μ E [] g k

def KerW : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × ℕ)) (g : ℝ → ℝ), LgFacts → Unimod → RCalc → (∃ k, IsKer μ E [] g k) → ∃ k, IsKer μ E w g k

end PositivityTheory.RgBcC.Fc
