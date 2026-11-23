import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Mult

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def bconv (g g' : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t, g t * g' (r - t)

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def EpowT (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s c a (EpowT s m c b f)

def gelT (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, EpowT s m a a f

def zAdj : List (Bool × ℕ) → (Mat n → V) → (Mat n → V)
  | [] => id
  | p :: w => fun h => zAdj w (((-1 : ℂ) ^ p.2) • gelT (!p.1) p.2 h)

end Ops

def kAdj (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Mat n → (E.V →L[ℂ] E.V) :=
  haveI := FiniteDimensional.complete ℂ E.V
  fun y => ContinuousLinearMap.adjoint (k y⁻¹)

def KReg {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (k : Mat n → (W →L[ℂ] W)) : Prop :=
  ContinuousOn k (GLs n) ∧ ∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0

def REq (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂

def Hyp : Prop := LgFacts ∧ Unimod ∧ RCalc ∧ WaveSpeed ∧ WaveEx ∧ KerUniq ∧ KerOne

def ClEig : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ),
  IsMult μ E k val T → ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x

def ClProd : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)) (val val' : Inf n → ℂ) (T T' : ℝ),
  IsMult μ E k val T → IsMult μ E k' val' T' →
    IsMult μ E (conv μ E k k') (val * val') (T + T') ∧ ∀ y ∈ GLs n, conv μ E k k' y = conv μ E k' k y

def ClAdj : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ),
  IsMult μ E k val T → ∃ val₁, IsMult μ E (kAdj E k) val₁ T ∧ ∀ χ, IsHerm χ → val₁ χ = conj (val χ)

def ActInt : Prop := LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V),
  KReg k → ContinuousOn f (GLs n) → ∀ x ∈ GLs n, Integrable (fun y : G n => k y.val (f (x * y.val))) μ

def ConvSum : Prop := LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (m m' : ℕ) (c : Fin m → ℂ) (c' : Fin m' → ℂ)
  (ks : Fin m → Mat n → (E.V →L[ℂ] E.V)) (ks' : Fin m' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)),
  (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) →
    ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x

def ConvAct : Prop := LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V),
  KReg k → KReg k' → ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E (conv μ E k k') f x = act μ E k (act μ E k' f) x

def ConvReg : Prop := LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)),
  KReg k → KReg k' → KReg (conv μ E k k') ∧ (REq E k' → REq E (conv μ E k k'))

def KerAgree : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k₁ k₂ : Mat n → (E.V →L[ℂ] E.V)),
  KReg k₁ → KReg k₂ → REq E k₁ → REq E k₂ → (∀ u, IsWave E u → Cpt (u 0) → act μ E k₁ (u 0) 1 = act μ E k₂ (u 0) 1) →
    ∀ y ∈ GLs n, k₁ y = k₂ y

def KerBasic : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (k : Mat n → (E.V →L[ℂ] E.V)),
  IsKer μ E w g k → KReg k ∧ REq E k ∧ KReg (kAdj E k) ∧ REq E (kAdj E k)

def BumpConv : Prop := ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' →
  IsBump (bconv g g') (T + T') ∧ bconv g g' = bconv g' g

def CoshConv : Prop := ∀ (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ), IsBump g T → IsBump g' T' →
  coshT (bconv g g') c = coshT g c * coshT g' c

def JointZ : Prop := ∀ (n : ℕ) (H V : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
  (F : H → Mat n → V) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry F) (Set.univ ×ˢ GLs n) →
    ContDiffOn ℝ ∞ (Function.uncurry fun h => zOp w (F h)) (Set.univ ×ˢ GLs n) ∧
    ContDiffOn ℝ ∞ (Function.uncurry fun h => Om (F h)) (Set.univ ×ˢ GLs n)

def IntZ : Prop := ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (F : ℝ → Mat n → V)
  (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), IsBump g T → ContDiffOn ℝ ∞ (Function.uncurry F) (Set.univ ×ˢ GLs n) →
    ∀ x ∈ GLs n, zOp w (fun y => ∫ t, (g t : ℂ) • F t y) x = ∫ t, (g t : ℂ) • zOp w (F t) x ∧
      Om (fun y => ∫ t, (g t : ℂ) • F t y) x = ∫ t, (g t : ℂ) • Om (F t) x

def IntSmooth : Prop := ∀ (n : ℕ) (H V : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V] (F : ℝ → H → Mat n → V) (g : ℝ → ℝ) (T : ℝ), IsBump g T →
  ContDiffOn ℝ ∞ (fun p : ℝ × H × Mat n => F p.1 p.2.1 p.2.2) (Set.univ ×ˢ (Set.univ ×ˢ GLs n)) →
    ContDiffOn ℝ ∞ (fun q : H × Mat n => ∫ t, (g t : ℂ) • F t q.1 q.2) (Set.univ ×ˢ GLs n)

def IntDeriv : Prop := ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (F : ℝ → ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), IsBump g T →
  ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × Mat n => F p.1 p.2.1 p.2.2) (Set.univ ×ˢ (Set.univ ×ˢ GLs n)) → ∀ x ∈ GLs n, ∀ s,
    deriv (fun s => ∫ t, (g t : ℂ) • F t s x) s = ∫ t, (g t : ℂ) • deriv (fun s => F t s x) s ∧
    iteratedDeriv 2 (fun s => ∫ t, (g t : ℂ) • F t s x) s = ∫ t, (g t : ℂ) • iteratedDeriv 2 (fun s => F t s x) s

def MixZ : Prop := ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (F : ℝ → Mat n → V) (w : List (Bool × ℕ)),
  ContDiffOn ℝ ∞ (Function.uncurry F) (Set.univ ×ˢ GLs n) → ∀ x ∈ GLs n, ∀ t,
    deriv (fun t => zOp w (F t) x) t = zOp w (fun y => deriv (fun t => F t y) t) x ∧
    iteratedDeriv 2 (fun t => zOp w (F t) x) t = zOp w (fun y => iteratedDeriv 2 (fun t => F t y) t) x

def ZLin : Prop := RCalc → ∀ n : ℕ, (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × ℕ)) (f h : Mat n → V) (a b : ℂ),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) →
      ContDiffOn ℝ ∞ (zOp w f) (GLs n) ∧ ContDiffOn ℝ ∞ (Om f) (GLs n) ∧
      ∀ x ∈ GLs n, zOp w (fun y => a • f y + b • h y) x = a • zOp w f x + b • zOp w h x ∧
        Om (fun y => a • f y + b • h y) x = a • Om f x + b • Om h x) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × ℕ)) (f f' : Mat n → V), Set.EqOn f f' (GLs n) →
    ∀ x ∈ GLs n, zOp w f x = zOp w f' x ∧ Om f x = Om f' x) ∧
  ∀ (E : KMod n) (w : List (Bool × ℕ)), ∀ f ∈ CE E, zOp w f ∈ CE E ∧ Om f ∈ CE E

def ZComm : Prop := RCalc → ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (w w' : List (Bool × ℕ)) (f : Mat n → V),
  ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, zOp w (zOp w' f) x = zOp w' (zOp w f) x ∧ Om (zOp w f) x = zOp w (Om f) x

def WaveZ : Prop := RCalc → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w : List (Bool × ℕ)),
  IsWave E u → IsWave E (fun t => zOp w (u t))

def WaveSym : Prop := RCalc → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u →
  ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × Mat n => (1 / 2 : ℂ) • (u (p.1 + p.2.1) p.2.2 + u (p.1 - p.2.1) p.2.2))
    (Set.univ ×ˢ (Set.univ ×ˢ GLs n)) ∧
  ∀ t₀, IsWave E (fun s x => (1 / 2 : ℂ) • (u (t₀ + s) x + u (t₀ - s) x))

def WaveInt : Prop := RCalc → ∀ (n : ℕ) (E : KMod n) (U : ℝ → ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ), IsBump g T →
  ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × Mat n => U p.1 p.2.1 p.2.2) (Set.univ ×ˢ (Set.univ ×ˢ GLs n)) → (∀ t, IsWave E (U t)) →
    IsWave E (fun s x => ∫ t, (g t : ℂ) • U t s x)

def DalemInt : Prop := ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T →
  IsBump g' T' → ∀ x ∈ GLs n,
    ∫ s, (g s : ℂ) • ∫ t, (g' t : ℂ) • ((1 / 2 : ℂ) • (u (t + s) x + u (t - s) x)) = ∫ r, (bconv g g' r : ℂ) • u r x

def WaveCptT : Prop := LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → Cpt (u 0) → ∀ t, Cpt (u t)

def EigWave : Prop := RCalc → ∀ (n : ℕ) (E : KMod n) (χ : Inf n) (f : Mat n → E.V), f ∈ CE E → IsEig χ f →
  IsWave E (fun t x => Complex.cosh (t * cas χ ^ (1 / 2 : ℂ)) • f x)

def ZOpEig : Prop := ∀ (n : ℕ) (E : KMod n) (χ : Inf n) (f : Mat n → E.V), f ∈ CE E → IsEig χ f →
  ∀ (w : List (Bool × ℕ)) (c : ℂ), ∀ x ∈ GLs n, zOp w (fun y => c • f y) x = (c * zVal w χ) • f x

def AdjPair : Prop := LgFacts → Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f h : Mat n → E.V),
  KReg k → ContinuousOn f (GLs n) → ContinuousOn h (GLs n) → Cpt f → Cpt h →
    ∫ y : G n, ⟪act μ E k f y.val, h y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪f y.val, act μ E (kAdj E k) h y.val⟫_ℂ ∂μ

def IBP : Prop := LgFacts → Unimod → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
  [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V)
  (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h →
    ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪f y.val, zAdj w h y.val⟫_ℂ ∂μ

def TransPoly : Prop := ∀ n m : ℕ, ∃ (N : ℕ) (c : Fin N → ℂ) (ws : Fin N → List ℕ),
  (∀ (A : Type) [Ring A] [Algebra ℂ A] (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    Formalism.REAL.etr (fun a b => X b a) m = ∑ j, c j • ((ws j).map (Formalism.REAL.etr X)).prod) ∧
  ∀ ψ : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (-ψ) m = ∑ j, c j * ((ws j).map (GlobalTheory.Dec.gelfVal ψ)).prod

def GelfSym : Prop := ∀ (n : ℕ) (ψ : Fin n → ℂ) (m : ℕ),
  (∀ σ : Equiv.Perm (Fin n), GlobalTheory.Dec.gelfVal (fun a => ψ (σ a)) m = GlobalTheory.Dec.gelfVal ψ m) ∧
  GlobalTheory.Dec.gelfVal (fun a => conj (ψ a)) m = conj (GlobalTheory.Dec.gelfVal ψ m)

def TransOp : Prop := RCalc → ∀ (n : ℕ) (s : Bool) (m : ℕ), ∃ (N : ℕ) (c : Fin N → ℂ) (ws : Fin N → List ℕ),
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ x ∈ GLs n, gelT s m f x = ∑ j, c j • zOp ((ws j).map fun k => (s, k)) f x) ∧
  ∀ ψ : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (-ψ) m = ∑ j, c j * ((ws j).map (GlobalTheory.Dec.gelfVal ψ)).prod

def ZAdjPoly : Prop := RCalc → ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (ws : Fin N → List (Bool × ℕ)),
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ x ∈ GLs n, zAdj w f x = ∑ j, c j • zOp (ws j) f x) ∧
  ∀ χ : Inf n, IsHerm χ → ∑ j, c j * zVal (ws j) χ = conj (zVal w χ)

def WaveSA : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) →
  ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ

def FundSec : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (φ : Mat n → E.V), ContinuousOn φ (GLs n) →
  (∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, φ (x * k.1) = E.ρ k⁻¹ (φ x)) →
  (∀ h ∈ CE E, Cpt h → ∫ y : G n, ⟪φ y.val, h y.val⟫_ℂ ∂μ = 0) → ∀ x ∈ GLs n, φ x = 0

def AdjWave : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)),
  IsBump g T → IsKer μ E w g k → ∀ u, IsWave E u → Cpt (u 0) →
    ∀ x ∈ GLs n, act μ E (kAdj E k) (u 0) x = zAdj w (fun y => ∫ t, (g t : ℂ) • u t y) x

end PositivityTheory.RgBcC.Mult
