import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

structure CxData (lam : Fin n → ℤ) (E : KMod n) (Fr : Mat n → (E.V →L[ℂ] E.V)) (ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V))
    (S : ℝ → (E.V →L[ℂ] E.V)) (Γ T : E.V →L[ℂ] E.V) : Prop where
  smooth : ContDiffOn ℝ ∞ Fr (GLs n)
  one : Fr 1 = 1
  mul : ∀ x ∈ GLs n, ∀ y ∈ GLs n, Fr (x * y) = Fr x * Fr y
  onK : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, Fr k.1 = E.ρ k
  car : ∀ H H' : Mat n, H.IsHermitian → H'.IsHermitian → ε H * ι H' + ι H' * ε H = (H * H').trace • 1
  frι : ∀ x ∈ GLs n, ∀ H : Mat n, H.IsHermitian → Fr x * ι H = ι (x * H * xᴴ) * Fr x
  frε : ∀ x ∈ GLs n, ∀ H : Mat n, H.IsHermitian → ε H * Fr x = Fr x * ε (xᴴ * H * x)
  Γsq : Γ * Γ = 1
  Γε : ∀ H, Γ * ε H = -(ε H * Γ)
  Γι : ∀ H, Γ * ι H = -(ι H * Γ)
  ΓFr : ∀ x ∈ GLs n, Γ * Fr x = Fr x * Γ
  ΓT : Γ * T = T * Γ
  Tsq : T * T = 1
  Tiso : ∀ v, ‖T v‖ = ‖v‖
  TK : ∀ k, T * E.ρ k = E.ρ k * T
  Tε : ∀ H, T * ε H = ε H * T
  Tι : ∀ H, T * ι H = ι H * T
  TD : T * (∑ p, ε (hb p) * fderiv ℝ Fr 1 (hb p)) = -((∑ p, ε (hb p) * fderiv ℝ Fr 1 (hb p)) * T)
  Ssmooth : ContDiff ℝ ∞ S
  S1 : S 1 = 1
  Sε : ∀ s H, S s * ε H = (s : ℂ) • (ε H * S s)
  Sder : ∀ s, deriv S s = ∑ p, ε (hb p) * S s * ι (hb p)
  SΓ : ∀ s, Γ * S s = S s * Γ
  S0sq : S 0 * S 0 = S 0
  S0Γ : Γ * S 0 = S 0
  sym_zero_comm_frame : ∀ x ∈ GLs n, S 0 * Fr x = Fr x * S 0
  time_comm_sym_zero : T * S 0 = S 0 * T
  S0θ : ∀ x ∈ GLs n, T * Fr (xᴴ⁻¹) * S 0 = Fr x * T * S 0
  eig : ∀ w, IsEig (infOf lam) fun x => Fr x⁻¹ (S 0 w)
  char : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
    LinearMap.trace ℂ E.V ((S 0 * Fr (diagonal z) * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) = conj (weylChar lam fun a => z a ^ 2)

def CxEx : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∃ E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T

def GelComm : Prop :=
  ∀ (n : ℕ) (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V'] (s : Bool) (m : ℕ)
    (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (gel s m f) (GLs n) ∧ ∀ g ∈ GLs n,
      (∀ X, gel s m (Rd X f) g = Rd X (gel s m f) g) ∧
      (∀ h ∈ GLs n, gel s m (fun y => f (h * y)) g = gel s m f (h * g) ∧ gel s m (fun y => f (y * h)) g = gel s m f (g * h)) ∧
      ∀ A : V →L[ℂ] V', gel s m (fun y => A (f y)) g = A (gel s m f g)

def GelN : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (blk : Fin n → ℕ) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    (∀ u : Mat n, (∀ a b, ¬ blk a < blk b → (u - 1) a b = 0) → ∀ g ∈ GLs n, f (u * g) = f g) →
    (∀ g ∈ GLs n, (∀ a b, blk a ≠ blk b → g a b = 0) → f g = 0) →
    ∀ s m, ∀ g ∈ GLs n, (∀ a b, blk a ≠ blk b → g a b = 0) → gel s m f g = 0

def FlagField : Prop :=
  ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ → ∃ H : Mat n → Mat n, ContDiffOn ℝ ∞ H (GLs n) ∧
    (∀ x ∈ GLs n, (H x).IsHermitian) ∧ (H 1 * H 1).trace ≠ 0 ∧
    (∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, H (x * k.1) = k.1ᴴ * H x * k.1) ∧
    (∀ q ∈ GLs n, W₁.map (Matrix.mulVecLin q) = W₁ → W₂.map (Matrix.mulVecLin q) = W₂ → ∀ x ∈ GLs n, H (q * x) = H x) ∧
    ∀ d ∈ GLs n, (fun v => d *ᵥ v) '' perp W₂ = W₁ → (fun v => d *ᵥ v) '' perp W₁ = W₂ → H d = -H 1

def GelFlag : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
    ∀ (A : Mat n → (V →L[ℂ] V)) (f : Mat n → V), ContDiffOn ℝ ∞ A (GLs n) → ContDiffOn ℝ ∞ f (GLs n) →
    (∀ q ∈ GLs n, W₁.map (Matrix.mulVecLin q) = W₁ → W₂.map (Matrix.mulVecLin q) = W₂ → ∀ x ∈ GLs n, A (q * x) = A x) →
    (∀ u ∈ nilSet W₁ W₂, ∀ x ∈ GLs n, f (u.val * x) = f x) →
    ∀ s m, ∀ x ∈ GLs n, gel s m (fun y => A y (f y)) x = A x (gel s m f x)

def NilUni : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → ∀ N : Subgroup (G n),
    (N : Set (G n)) = nilSet W₁ W₂ → IsClosed (N : Set (G n)) ∧ ∀ (ν : Measure N) [ν.IsHaarMeasure], ν.IsInvInvariant

def KerZero : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (κ : Mat n → (E.V →L[ℂ] E.V)), ContinuousOn κ (GLs n) →
    (∀ y ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, κ (y * k.1) = κ y * E.ρ k) →
    (∀ f ∈ CE E, (∃ R, ∀ y ∈ GLs n, R < lg y → f y = 0) → ∫ y : G n, κ y.val (f y.val) ∂μ = 0) → ∀ y ∈ GLs n, κ y = 0

def VCSt : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
      (val : Inf n → ℂ) (τ : ℝ), IsMult μ E k val τ →
      ∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
        (fun v => d.val *ᵥ v) '' perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' perp W₁ = W₂ →
        ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
          ∫ u : N, phiOf E T k (u * d) ∂ν = 0

def Ld {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Mat n) (k : Mat n → V) : Mat n → V :=
  fun y => -fderiv ℝ k y (X * y)

def Chain : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
      (val : Inf n → ℂ) (τ : ℝ), IsMult μ E k val τ → ∀ y ∈ GLs n, Γ * k y = k y * Γ ∧
        ∑ p, ε (hb p) * (Ld (hb p) k y + fderiv ℝ Fr 1 (hb p) * k y) =
          ∑ p, (-(Rd (hb p) k y) * ε (hb p) + k y * ε (hb p) * fderiv ℝ Fr 1 (hb p))

def hOf (v : Fin n × Fin n → ℝ) : Mat n := ∑ p, (v p : ℂ) • hb p

def cone (n : ℕ) : Set (Fin n × Fin n → ℝ) := {v | (hOf v).PosDef}

def ConeSt : Prop :=
  ∀ n : ℕ, IsOpen (cone n) ∧ Convex ℝ (cone n) ∧ ∃ σ : (Fin n × Fin n → ℝ) → Mat n, ContDiffOn ℝ ∞ σ (cone n) ∧
    (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) ∧
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ c : ℝ, 0 < c ∧
      ∀ F : Mat n → ℂ, ContinuousOn F (GLs n) → (∃ R, ∀ y ∈ GLs n, R < lg y → F y = 0) →
        (∀ y ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (y * k.1) = F y) →
        ∫ y : G n, F y.val ∂μ = c * ∫ v in cone n, F (σ v) * ((hOf v).det ^ n)⁻¹

def Homot : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e c : I → (V →L[ℂ] V)) (S : ℝ → (V →L[ℂ] V)) (Γ : V →L[ℂ] V) (U : Set (I → ℝ)) (o : I → ℝ)
    (K : (I → ℝ) × (I → ℝ) → (V →L[ℂ] V)), IsOpen U → Convex ℝ U → o ∈ U →
    (∀ i j, e i * c j + c j * e i = if i = j then 1 else 0) → (∀ i, Γ * e i = -(e i * Γ)) → (∀ i, Γ * c i = -(c i * Γ)) →
    (∀ s, Γ * S s = S s * Γ) → ContDiff ℝ ∞ S → (∀ s i, S s * e i = (s : ℂ) • (e i * S s)) →
    (∀ s, deriv S s = ∑ i, e i * S s * c i) → ContDiffOn ℝ ∞ K (U ×ˢ U) → (∀ y, Γ * K y = K y * Γ) →
    (∀ y ∈ U ×ˢ U, ∑ i, e i * fderiv ℝ K y (Pi.single i 1, 0) + ∑ i, fderiv ℝ K y (0, Pi.single i 1) * e i = 0) →
    (∃ C ⊆ U, IsCompact C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ U, v ∉ C → ∀ᶠ y in nhds (s • v + (1 - s) • o, v), K y = 0) →
    ∫ v in U, LinearMap.trace ℂ V ((Γ * S 1 * K (v, v) : V →L[ℂ] V) : V →ₗ[ℂ] V) =
      ∫ v in U, LinearMap.trace ℂ V ((Γ * S 0 * K (o, v) : V →L[ℂ] V) : V →ₗ[ℂ] V)

def SuppSt : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) → ∀ R : ℝ, ∃ R' : ℝ,
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ GLs n, ∀ y ∈ GLs n, x * xᴴ = (s : ℂ) • (y * yᴴ) + ((1 - s : ℝ) : ℂ) • (1 : Mat n) →
      lg (x⁻¹ * diagonal z * yᴴ⁻¹) ≤ R → lg y ≤ R'

def LSt : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
      (val : Inf n → ℂ) (τ : ℝ), IsMult μ E k val τ →
      ∀ (d : G n) (z : Fin n → ℂ), d.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
        Integrable (fun x => phiOf E T k (tw x d)) μ ∧
          ∫ x, phiOf E T k (tw x d) ∂μ = val (infOf lam) * conj (weylChar lam fun a => z a ^ 2)

def ChainOf : Prop := WaveEx → WaveSpeed → GelComm → Chain
def GelFlagOf : Prop := GelComm → GelN → GelFlag
def VCOf : Prop := WaveEx → WaveSpeed → MultAlg → GelComm → GelFlag → FlagField → NilUni → KerZero → VCSt
def LOf : Prop := WaveEx → WaveSpeed → KerEx → MultAlg → Chain → ConeSt → Homot → SuppSt → LSt

theorem lef_of (h0 : CxEx) (h1 : VCSt) (h2 : LSt) : Lef := by
  intro n lam hlam
  obtain ⟨E, Fr, ε, ι, S, Γ, T, h⟩ := h0 n lam hlam
  exact ⟨E, T, h.TK, h.Tiso, h.Tsq, fun μ _ k val τ hk =>
    ⟨h1 n lam E Fr ε ι S Γ T h μ k val τ hk, h2 n lam E Fr ε ι S Γ T h μ k val τ hk⟩⟩

end PositivityTheory.RgBcC
