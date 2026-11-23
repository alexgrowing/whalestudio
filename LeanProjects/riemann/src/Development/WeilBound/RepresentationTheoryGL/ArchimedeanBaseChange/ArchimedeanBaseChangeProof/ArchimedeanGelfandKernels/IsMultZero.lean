import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat G th tw)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def GLs (n : ℕ) : Set (Mat n) := {g | g.det ≠ 0}

def lg (y : Mat n) : ℝ := Real.log (1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2))

structure KMod (n : ℕ) : Type 1 where
  V : Type
  [nacg : NormedAddCommGroup V]
  [ips : InnerProductSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  ρ : Matrix.unitaryGroup (Fin n) ℂ →* (V →L[ℂ] V)
  iso : ∀ k v, ‖ρ k v‖ = ‖v‖
  cont : Continuous ρ

attribute [instance] KMod.nacg KMod.ips KMod.fd

def KMod.triv (n : ℕ) : KMod n := ⟨ℂ, 1, fun _ _ => rfl, continuous_const⟩

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Rd (X : Mat n) (f : Mat n → V) : Mat n → V := fun g => fderiv ℝ f g (g * X)

def Eu (s : Bool) (a b : Fin n) (f : Mat n → V) : Mat n → V :=
  (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) f + (if s then -Complex.I else Complex.I) • Rd (Matrix.single a b Complex.I) f)

def Epow (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s a c (Epow s m c b f)

def gel (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, Epow s m a a f

def Om (f : Mat n → V) : Mat n → V := (2 : ℂ) • (gel true 2 f + gel false 2 f)

def zOp : List (Bool × ℕ) → (Mat n → V) → (Mat n → V)
  | [] => id
  | p :: w => fun f => gel p.1 p.2 (zOp w f)

end Ops

abbrev Inf (n : ℕ) := Bool → Fin n → ℂ

def zVal (w : List (Bool × ℕ)) (χ : Inf n) : ℂ := (w.map fun p => GlobalTheory.Dec.gelfVal (χ p.1) p.2).prod

def cas (χ : Inf n) : ℂ := 2 * (GlobalTheory.Dec.gelfVal (χ true) 2 + GlobalTheory.Dec.gelfVal (χ false) 2)

def coshT (g : ℝ → ℝ) (c : ℂ) : ℂ := ∫ t, (g t : ℂ) * Complex.cosh (t * c ^ (1 / 2 : ℂ))

def CE (E : KMod n) : Set (Mat n → E.V) :=
  {f | ContDiffOn ℝ ∞ f (GLs n) ∧ ∀ g ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, f (g * k.1) = E.ρ k⁻¹ (f g)}

def IsWave (E : KMod n) (u : ℝ → Mat n → E.V) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n) ∧ (∀ t, u t ∈ CE E) ∧
    (∀ t, ∀ g ∈ GLs n, iteratedDeriv 2 (fun s => u s g) t = Om (u t) g) ∧ ∀ g ∈ GLs n, deriv (fun s => u s g) 0 = 0

def IsBump (g : ℝ → ℝ) (T : ℝ) : Prop := ContDiff ℝ ∞ g ∧ (∀ t, g (-t) = g t) ∧ ∀ t, T < |t| → g t = 0

def IsEig {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (χ : Inf n) (f : Mat n → V) : Prop :=
  ∀ s m, ∀ g ∈ GLs n, gel s m f g = GlobalTheory.Dec.gelfVal (χ s) m • f g

def IsHerm (χ : Inf n) : Prop := ∃ σ : Equiv.Perm (Fin n), ∀ a, χ false (σ a) = -conj (χ true a)

section Ker

variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

def act (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V) : Mat n → E.V := fun x => ∫ y : G n, k y.val (f (x * y.val)) ∂μ

def IsKer (w : List (Bool × ℕ)) (g : ℝ → ℝ) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  ContDiffOn ℝ ∞ k (GLs n) ∧ (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) ∧
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) ∧
    ∀ u, IsWave E u → ∀ x ∈ GLs n, act μ E k (u 0) x = zOp w (fun x' => ∫ t, (g t : ℂ) • u t x') x

def IsMult (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → List (Bool × ℕ)) (g : Fin m → ℝ → ℝ) (ks : Fin m → Mat n → (E.V →L[ℂ] E.V)),
    (∀ i, IsBump (g i) T ∧ IsKer μ E (w i) (g i) (ks i)) ∧ (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) ∧
      ∀ χ, val χ = ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ)

theorem isMult_zero (T : ℝ) : IsMult μ E 0 0 T :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp, by simp⟩

def conv (k k' : Mat n → (E.V →L[ℂ] E.V)) : Mat n → (E.V →L[ℂ] E.V) :=
  fun x => ∫ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) ∂μ

def phiOf (Tθ : E.V →L[ℂ] E.V) (k : Mat n → (E.V →L[ℂ] E.V)) (y : G n) : ℂ :=
  LinearMap.trace ℂ E.V ((k y.val * Tθ : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)

end Ker

def WaveEx : Prop := ∀ (n : ℕ) (E : KMod n), ∀ f ∈ CE E, ∃ u, IsWave E u ∧ ∀ g ∈ GLs n, u 0 g = f g

def WaveSpeed : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (t : ℝ), ∀ x ∈ GLs n,
    (∀ y ∈ GLs n, lg y ≤ c * (1 + |t|) → u 0 (x * y) = 0) → u t x = 0

def KerEx : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    (∀ (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ), IsBump g T → ∃ k, IsKer μ E w g k) ∧
    ∀ k val (T : ℝ), 0 ≤ T → IsMult μ E k val T → ∀ y ∈ GLs n, c * (1 + T) < lg y → k y = 0

def MultAlg : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k k' : Mat n → (E.V →L[ℂ] E.V)) (val val' : Inf n → ℂ) (T T' : ℝ), IsMult μ E k val T → IsMult μ E k' val' T' →
      IsMult μ E (conv μ E k k') (val * val') (T + T') ∧ (∀ y ∈ GLs n, conv μ E k k' y = conv μ E k' k y) ∧
      (haveI := FiniteDimensional.complete ℂ E.V
        ∃ val₁, IsMult μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) val₁ T ∧ ∀ χ, IsHerm χ → val₁ χ = conj (val χ)) ∧
      ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x

def perp (W : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ) := {v | ∀ w ∈ W, star w ⬝ᵥ v = 0}

def nilSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : Set (G n) :=
  {u | (∀ v, (u.val - 1) *ᵥ v ∈ W₂) ∧ (∀ v ∈ W₂, (u.val - 1) *ᵥ v ∈ W₁) ∧ ∀ v ∈ W₁, (u.val - 1) *ᵥ v = 0}

def weylChar (lam : Fin n → ℤ) (γ : Fin n → ℂ) : ℂ :=
  (Matrix.of fun i j : Fin n => γ i ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det /
    (Matrix.of fun i j : Fin n => γ i ^ (n - 1 - (j : ℕ))).det

def infOf (lam : Fin n → ℤ) : Inf n := fun s a =>
  (if s then 1 else -1) * ((lam a : ℂ) + ((n : ℂ) - 1) / 2 - (a : ℕ))

def Lef : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∃ (E : KMod n) (Tθ : E.V →L[ℂ] E.V), (∀ k, Tθ * E.ρ k = E.ρ k * Tθ) ∧
    (∀ v, ‖Tθ v‖ = ‖v‖) ∧ Tθ * Tθ = 1 ∧
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
      (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T →
      (∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
        (fun v => d.val *ᵥ v) '' perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' perp W₁ = W₂ →
        ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
          ∫ u : N, phiOf E Tθ k (u * d) ∂ν = 0) ∧
      ∀ (d : G n) (z : Fin n → ℂ), d.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
        Integrable (fun x => phiOf E Tθ k (tw x d)) μ ∧
          ∫ x, phiOf E Tθ k (tw x d) ∂μ = val (infOf lam) * conj (weylChar lam fun a => z a ^ 2)

def Laplace : Prop :=
  ∀ (a b : ℕ) (γ : Fin (a + b) → ℂ) (m : Fin (a + b) → ℤ),
    (Matrix.of fun i j => γ i ^ m j).det =
      ∑ S : {S : Finset (Fin (a + b)) // S.card = a ∧ Sᶜ.card = b},
        (-1) ^ (∑ s ∈ S.1, (s : ℕ) + ∑ i ∈ range a, i) *
          (Matrix.of fun i j : Fin a => γ (Fin.castAdd b i) ^ m (S.1.orderEmbOfFin S.2.1 j)).det *
          (Matrix.of fun i j : Fin b => γ (Fin.natAdd a i) ^ m (S.1ᶜ.orderEmbOfFin S.2.2 j)).det

def ValSep : Prop :=
  ∀ (n : ℕ) (χ χ' : Inf n), (∃ g T, IsBump g T ∧ coshT g (cas χ) ≠ 0) ∧
    ((∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = GlobalTheory.Dec.gelfVal (χ' s) m) → ∀ s, ∃ σ : Equiv.Perm (Fin n), ∀ a, χ' s (σ a) = χ s a)

end PositivityTheory.RgBcC
