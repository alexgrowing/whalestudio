import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def bs (p : Bool × Fin n × Fin n) : Mat n := Matrix.single p.2.1 p.2.2 (if p.1 then 1 else Complex.I)

def Rw {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] : List (Bool × Fin n × Fin n) → (Mat n → V) → (Mat n → V)
  | [] => id
  | p :: w => fun f => Rd (bs p) (Rw w f)

def Cpt {V : Type} [Zero V] (f : Mat n → V) : Prop := ∃ R, ∀ y ∈ GLs n, R < lg y → f y = 0

def AlgEst : Prop :=
  ∀ (V ι : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] (X : ι → Module.End ℂ V) (c : ι → ι → ι → ℝ),
    (∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) → (∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) →
    ∀ w : List ι, ∃ C : ℝ, ∀ u, ‖(w.map X).prod u‖ ≤ C * ∑ j ∈ range (w.length + 1), ‖((-∑ i, X i * X i) ^ j) u‖

def LgFacts : Prop :=
  ∀ n : ℕ, (∀ x ∈ GLs n, ∀ y ∈ GLs n, lg (x * y) ≤ lg x + lg y) ∧ (∀ x ∈ GLs n, lg x⁻¹ = lg x) ∧
    (∀ x ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, lg (k₁.1 * x * k₂.1) = lg x) ∧ ContDiffOn ℝ ∞ lg (GLs n) ∧
    (∀ R, IsCompact {y : G n | lg y.val ≤ R}) ∧ (∀ R, IsCompact {y : Mat n | y ∈ GLs n ∧ lg y ≤ R}) ∧
    ∃ C : ℝ, ∀ x ∈ GLs n, ∀ p, |fderiv ℝ lg x (x * bs p)| ≤ C

def Unimod : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure],
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant

def SobG : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure],
    ∃ (S : Finset (List (Bool × Fin n × Fin n))) (r C : ℝ), ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n,
        ‖f x‖ ^ 2 ≤ C * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w f (x * y.val)‖ ^ 2 ∂μ

def RCalc : Prop :=
  ∀ (n : ℕ), (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ X, ContDiffOn ℝ ∞ (Rd X f) (GLs n)) ∧
      (∀ X Y, ∀ g ∈ GLs n, Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g) ∧
      (∀ s m X, ∀ g ∈ GLs n, Rd X (gel s m f) g = gel s m (Rd X f) g) ∧
      (∀ s m, ∀ x ∈ GLs n, ∀ g ∈ GLs n, gel s m (fun y => f (x * y)) g = gel s m f (x * g) ∧
        gel s m (fun y => f (y * x)) g = gel s m f (g * x))) ∧
    (∀ (E : KMod n), ∀ f ∈ CE E, ∀ s m, gel s m f ∈ CE E) ∧
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f → ∀ X, ∫ y : G n, Rd X f y.val ∂μ = 0

def WaveCpt : Prop := ∀ (n : ℕ) (E : KMod n), ∀ f ∈ CE E, Cpt f → ∃ u, IsWave E u ∧ ∀ g ∈ GLs n, u 0 g = f g

def KerUniq : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (U : Set (Mat n)), IsOpen U → U ⊆ GLs n →
    (∀ y ∈ U, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, y * k₂.1 ∈ U) → ContinuousOn k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂) →
    (∀ f ∈ CE E, Cpt f → (∀ y ∈ GLs n, y ∉ U → f y = 0) → act μ E k f 1 = 0) → ∀ y ∈ U, k y = 0

def KerOne : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ), IsBump g T → ∃ k, IsKer μ E w g k

def AsmSpeed : Prop := LgFacts → Unimod → RCalc → WaveSpeed
def AsmCpt : Prop := LgFacts → Unimod → RCalc → SobG → WaveCpt
def AsmEx : Prop := LgFacts → RCalc → WaveSpeed → WaveCpt → WaveEx
def AsmKerOne : Prop := LgFacts → Unimod → RCalc → SobG → AlgEst → WaveSpeed → KerOne
def AsmKerEx : Prop := LgFacts → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → KerEx
def AsmMult : Prop := LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → MultAlg

end PositivityTheory.RgBcC
