import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure FCalc (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M) (T : H →L[ℂ] H) where
  Φ : C₀(ℝ, ℂ) →L[ℂ] (H →L[ℂ] H)
  map_mul : ∀ g h, Φ (g * h) = Φ g * Φ h
  map_star : ∀ g, Φ (star g) = ContinuousLinearMap.adjoint (Φ g)
  norm_le : ∀ g, ‖Φ g‖ ≤ ‖g‖
  res : ∀ g : C₀(ℝ, ℂ), (∀ y, g y = ((1 + y ^ 2)⁻¹ : ℝ)) → Φ g = T
  omega : ∀ g h : C₀(ℝ, ℂ), (∀ y, h y = y * g y) → ∀ (x : H) (v : M), (v : H) = Φ g x → (Ω v : H) = Φ h x
  comm : ∀ S : H →L[ℂ] H, (∀ x : M, ∃ v : M, (v : H) = S x ∧ (Ω v : H) = S (Ω x)) → ∀ g, S * Φ g = Φ g * S

def AbsFC : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M)
    (T : H →L[ℂ] H), Dense (M : Set H) → (∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ) →
    (∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x) → (∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) →
    Nonempty (FCalc H M Ω T)

def AbsCut : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M)
    (T : H →L[ℂ] H) (F : FCalc H M Ω T) (c : ℝ) (x : H),
    (∀ g, ∃ v : M, (v : H) = F.Φ g x ∧ (⟪(Ω v : H), v⟫_ℂ).re ≤ c * ‖(v : H)‖ ^ 2) →
    ∀ g : C₀(ℝ, ℂ), (∀ y, y ≤ c → g y = 0) → F.Φ g x = 0

def Friedrichs : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (D : Submodule ℂ H) (A : D →ₗ[ℂ] H),
    (∀ x y : D, ⟪A x, y⟫_ℂ = ⟪(x : H), A y⟫_ℂ) → (∀ x : D, ‖(x : H)‖ ^ 2 ≤ (⟪A x, x⟫_ℂ).re) →
    ∃ R : H →L[ℂ] H, IsSelfAdjoint R ∧ ‖R‖ ≤ 1 ∧ (∀ x : D, R (A x) = x) ∧
      ∀ U : H →L[ℂ] H, ContinuousLinearMap.adjoint U * U = 1 → U * ContinuousLinearMap.adjoint U = 1 →
        (∀ x : D, ∃ y : D, (y : H) = U x ∧ A y = U (A x)) →
        (∀ x : D, ∃ y : D, (y : H) = ContinuousLinearMap.adjoint U x ∧ A y = ContinuousLinearMap.adjoint U (A x)) →
        U * R = R * U

def OneParam : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (φ : ℝ → (V →L[ℂ] V)),
    Continuous φ → φ 0 = 1 → (∀ s t, φ (s + t) = φ s * φ t) → ∃ A : V →L[ℂ] V, ∀ t, HasDerivAt φ (A * φ t) t

def toC0 (f : ℝ → ℂ) : C₀(ℝ, ℂ) :=
  @dite _ (Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0)) (Classical.dec _) (fun h => ⟨⟨f, h.1⟩, h.2⟩) (fun _ => 0)

def cut (c y : ℝ) : ℝ := max 0 (min 1 (c + 1 - y))

def chj (j : ℕ) (t y : ℝ) : ℂ :=
  ((y : ℂ) ^ (1 / 2 : ℂ)) ^ j * (if Even j then Complex.cosh else Complex.sinh) (t * (y : ℂ) ^ (1 / 2 : ℂ))

def wv (c : ℝ) (N j : ℕ) (t y : ℝ) : ℂ := ((cut c y * ((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * chj j t y

def Fcurve : Prop :=
  ∀ (c : ℝ) (N j : ℕ), j + 2 ≤ 4 * N → ∀ t : ℝ,
    (Continuous (wv c N j t) ∧ Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0)) ∧
      HasDerivAt (fun s => toC0 (wv c N j s)) (toC0 (wv c N (j + 1) t)) t

def WvAlg : Prop :=
  ∀ (c : ℝ) (N : ℕ) (t y : ℝ), wv c N 2 t y = y * wv c N 0 t y ∧ wv c N 1 0 y = 0 ∧
    wv c N 0 0 y = ((cut c y * ((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) ∧
    ∀ j, wv c (N + 1) j t y = (((1 + y ^ 2)⁻¹ : ℝ) : ℂ) * wv c N j t y

section Conc

variable {n : ℕ} [MeasurableSpace (G n)]

def cls (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : Mat n → V) : Lp V 2 μ :=
  @dite _ (MemLp (fun y : G n => f y.val) 2 μ) (Classical.dec _) (fun h => h.toLp _) (fun _ => 0)

def Sob (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ f (GLs n) ∧ ∀ w, MemLp (fun y : G n => Rw w f y.val) 2 μ

def Msob (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Submodule ℂ (Lp V 2 μ) :=
  Submodule.span ℂ {x | ∃ f : Mat n → V, Sob μ f ∧ cls μ f = x}

def rR (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (h : G n) :
    Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  @dite _ (MeasurePreserving (fun y : G n => y * h) μ μ) (Classical.dec _)
    (fun hh => (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => y * h) hh).toContinuousLinearMap) (fun _ => 0)

def IsSec (E : KMod n) (f : Mat n → E.V) : Prop :=
  ∀ g ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, f (g * k.1) = E.ρ k⁻¹ (f g)

end Conc

def ClsFacts : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], Unimod →
    (∀ f f' : Mat n → V, ContinuousOn f (GLs n) → ContinuousOn f' (GLs n) → MemLp (fun y : G n => f y.val) 2 μ →
      MemLp (fun y : G n => f' y.val) 2 μ → cls μ f = cls μ f' → ∀ g ∈ GLs n, f g = f' g) ∧
    (∀ (a : ℂ) (f f' : Mat n → V), MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => f' y.val) 2 μ →
      cls μ (a • f + f') = a • cls μ f + cls μ f') ∧
    (∀ (f f' : Mat n → V), (∀ g ∈ GLs n, f g = f' g) → cls μ f = cls μ f') ∧
    (∀ (h : G n) (f : Mat n → V), MemLp (fun y : G n => f y.val) 2 μ →
      rR μ V h (cls μ f) = cls μ (fun y => f (y * h.val))) ∧
    ∀ (A : V →L[ℂ] V) (f : Mat n → V), MemLp (fun y : G n => f y.val) 2 μ →
      A.compLpL 2 μ (cls μ f) = cls μ (fun y => A (f y))

def SobOps : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → Unimod → RCalc → ∀ f : Mat n → V, Sob μ f →
    Sob μ (Om f) ∧ (∀ w, Sob μ (Rw w f)) ∧ (∀ w, ∀ g ∈ GLs n, Rw w (Om f) g = Om (Rw w f) g) ∧
    (∀ (a : ℂ) (f' : Mat n → V), Sob μ f' → Sob μ (a • f + f') ∧ ∀ g ∈ GLs n, Om (a • f + f') g = a • Om f g + Om f' g) ∧
    ∀ (h : G n) (A : V →L[ℂ] V), Sob μ (fun y => A (f (y * h.val))) ∧
      ∀ g ∈ GLs n, Om (fun y => A (f (y * h.val))) g = A (Om f (g * h.val))

def CptSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → RCalc → ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) →
    Cpt f → Sob μ f ∧ Cpt (Om f)

def OmFormula : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ g ∈ GLs n, Om f g = ∑ a, ∑ c, (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g -
      Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g)

def IbpSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → Unimod → RCalc → ∀ f f' : Mat n → V, Sob μ f → Sob μ f' →
    ∀ X : Mat n, ⟪cls μ (Rd X f), cls μ f'⟫_ℂ = -⟪cls μ f, cls μ (Rd X f')⟫_ℂ

def DenseD : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts →
    Dense {x : Lp V 2 μ | ∃ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) ∧ Cpt f ∧ cls μ f = x}

def SecBound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    LgFacts → Unimod → RCalc → ∃ c : ℝ, ∀ f : Mat n → E.V, Sob μ f → IsSec E f →
      (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2

def PresSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (S : Lp V 2 μ →L[ℂ] Lp V 2 μ),
    LgFacts → Unimod → RCalc → SobG → (∀ h : G n, S * rR μ V h = rR μ V h * S) →
    ∀ f : Mat n → V, Sob μ f → ∃ f', Sob μ f' ∧ cls μ f' = S (cls μ f) ∧ ∀ w, cls μ (Rw w f') = S (cls μ (Rw w f))

def ConcT : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    LgFacts → Unimod → RCalc → SobG → PresSob → Friedrichs → ClsFacts → SobOps → CptSob → OmFormula → IbpSob → DenseD →
    (∀ x ∈ Msob μ V, ∃ f, Sob μ f ∧ cls μ f = x) ∧
    ∃ (Ω : Msob μ V →ₗ[ℂ] Msob μ V) (T : Lp V 2 μ →L[ℂ] Lp V 2 μ),
      Dense (Msob μ V : Set (Lp V 2 μ)) ∧ (∀ x y : Msob μ V, ⟪(Ω x : Lp V 2 μ), y⟫_ℂ = ⟪(x : Lp V 2 μ), Ω y⟫_ℂ) ∧
      (∀ x : Msob μ V, ∃ v : Msob μ V, (v : Lp V 2 μ) = T x ∧ (v : Lp V 2 μ) + (Ω (Ω v) : Lp V 2 μ) = x) ∧
      (∀ x : Msob μ V, T ((x : Lp V 2 μ) + (Ω (Ω x) : Lp V 2 μ)) = x) ∧
      ∀ (f : Mat n → V) (hf : cls μ f ∈ Msob μ V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp V 2 μ) = cls μ (Om f)

def CurveJoint : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (U : ℕ → ℝ → Mat n → V),
    LgFacts → RCalc → SobG → (∀ j t, Sob μ (U j t)) →
    (∀ j w t, HasDerivAt (fun s => cls μ (Rw w (U j s))) (cls μ (Rw w (U (j + 1) t))) t) →
    ContDiffOn ℝ ∞ (Function.uncurry (U 0)) (Set.univ ×ˢ GLs n) ∧
      ∀ j t, ∀ x ∈ GLs n, HasDerivAt (fun s => U j s x) (U (j + 1) t x) t

def Asm1 : Prop :=
  AbsFC → AbsCut → Fcurve → WvAlg → ClsFacts → SobOps → CptSob → SecBound → PresSob → ConcT → CurveJoint →
    Friedrichs → OmFormula → IbpSob → DenseD → AsmCpt

end PositivityTheory.RgBcC.Fc
