import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Rapid (h : C₀(ℝ, ℂ)) : Prop := ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y

def lTr {n : ℕ} {V : Type} (x : G n) (f : Mat n → V) : Mat n → V := fun y => f (x.val * y)

def secCls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) : Set (Lp E.V 2 μ) :=
  {x | ∃ f, Sob μ f ∧ IsSec E f ∧ cls μ f = x}

def Std {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ) : Prop :=
  LgFacts ∧ Unimod ∧ RCalc ∧ SobG ∧ AlgEst ∧ WaveSpeed ∧ WaveCpt ∧ CalcSteps ∧ SmoothOp ∧ PWdecay ∧
    (∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x) ∧
    (∀ x y : Msob μ E.V, ⟪(Ω x : Lp E.V 2 μ), y⟫_ℂ = ⟪(x : Lp E.V 2 μ), Ω y⟫_ℂ) ∧
    (∀ x : Msob μ E.V, ∃ v : Msob μ E.V, (v : Lp E.V 2 μ) = T x ∧ (v : Lp E.V 2 μ) + (Ω (Ω v) : Lp E.V 2 μ) = x) ∧
    (∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) ∧
    (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) ∧
    ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2

def Row {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (h : C₀(ℝ, ℂ)) (v : E.V) (f : Mat n → E.V) : Prop :=
  Sob μ f ∧ IsSec E f ∧ ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ → Sob μ f' → IsSec E f' →
    cls μ f' = F.Φ h (cls μ φ) → ⟪cls μ f, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def FactorRapid : Prop :=
  ∀ h : C₀(ℝ, ℂ), Rapid h → ∃ h₁ h₂ : C₀(ℝ, ℂ), Rapid h₁ ∧ Rapid h₂ ∧ Rapid (star h₂) ∧ h = h₁ * h₂

def EvAdj : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ κ ∈ closure (secCls μ E), ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ →
      Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ φ) → ⟪κ, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def RowExists : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ f, Row μ E F h v f

def RowMatrix : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), (∀ v : E.V, ∃ f, Row μ E F h v f) →
      ∃ A : Mat n → (E.V →L[ℂ] E.V), ∀ v, Row μ E F h v (fun y => A y v)

def AdjSmooth : Prop :=
  ∀ (W V : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (A : W → (V →L[ℂ] V)) (s : Set W),
    (∀ v, ContDiffOn ℝ ∞ (fun y => A y v) s) → ContDiffOn ℝ ∞ (fun y => ContinuousLinearMap.adjoint (A y)) s

def LtSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → Unimod → RCalc →
    ∀ (x : G n) (f : Mat n → V), Sob μ f → Sob μ (lTr x f) ∧ ∀ g ∈ GLs n, Om (lTr x f) g = Om f (x.val * g)

def LtComm : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (x : G n) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → cls μ f' = F.Φ h (cls μ f) →
      cls μ (lTr x f') = F.Φ h (cls μ (lTr x f))

def RowLeft : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), Rapid h → (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ y ∈ GLs n, ∀ v, A (k.1 * y) v = A y (E.ρ k⁻¹ v)

def ActFormula : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ f ∈ CE E, Cpt f → ∀ f', Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ f) →
        ∀ x ∈ GLs n, act μ E (fun y => ContinuousLinearMap.adjoint (A y)) f x = f' x

def WaveRep : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ f ∈ CE E, Cpt f → ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b

def WaveUniq : Prop :=
  WaveSpeed → CalcSteps → RCalc → ∀ (n : ℕ) (E : KMod n) (u u' : ℝ → Mat n → E.V), IsWave E u → IsWave E u' →
    (∀ x ∈ GLs n, u 0 x = u' 0 x) → ∀ t, ∀ x ∈ GLs n, u t x = u' t x

def PhiRes : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ N : ℕ, 1 ≤ N →
      F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) = F.Φ (toC0 (hg c g)) * T ^ N

def WaveInt : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N → IsWave E U →
      (∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b) →
      ∀ f', Sob μ f' → cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b →
        ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • U t x = f' x

def SupportRow : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ) (h : C₀(ℝ, ℂ)), IsBump g T₀ → Rapid h →
      (∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
        cls μ f' = F.Φ h (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x) →
      ∃ R : ℝ, ∀ (v : E.V) (f : Mat n → E.V), Row μ E F h v f → ∀ y ∈ GLs n, R < lg y → f y = 0

end GlobalTheory.CompanionTheory.KerFc
