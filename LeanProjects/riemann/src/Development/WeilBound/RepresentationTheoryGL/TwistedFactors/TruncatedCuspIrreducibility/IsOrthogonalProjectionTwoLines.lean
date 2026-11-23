import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay

noncomputable section

open MeasureTheory NumberField Set
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core
open scoped ENNReal NumberField.AdeleRing InnerProductSpace

namespace PositivityTheory.Rg.Tf.Adel

open PositivityTheory.Rg.Tf.IntegralApplyAeEq

variable {K : Type} [Field K] [NumberField K]

abbrev Eu (d : ℕ) : Type := EuclideanSpace ℂ (Fin d)

structure Line (μ : Measure (G1 K (2 + 2))) {μ₂ : Measure (G1 K 2)} (τ₁ τ₂ : Submodule ℂ (L2 μ₂))
    (D : TypeDat K (2 + 2)) (d : ℕ) where
  sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)
  inj : Function.Injective sec
  onto : ∀ f, f ∈ LinearMap.range sec ↔ IsSec τ₁ τ₂ f ∧ D.Fix f
  J : L (Eu d) →ₗᵢ[ℂ] L2 μ
  spec : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) →
    Reps μ (J u) (theta β (sec v))

def flat (z : ℂ) (f : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) : ℂ := Complex.exp ((z + 2) * (HP 2 2 x : ℂ)) * f x

def IsOrthogonalProjectionTwoLines {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint P ∧ P ∘L P = P ∧ ∀ h, P h = 0 ↔ (∀ u, ⟪J u, h⟫_ℂ = 0) ∧ ∀ v, ⟪J' v, h⟫_ℂ = 0

def IsGal {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (σ : K ≃+* K) (θ : Twist μ) : Prop :=
  ∃ s : 𝔸[K] ≃+* 𝔸[K], Continuous s ∧ (∀ x : K, s (algebraMap K 𝔸[K] x) = algebraMap K 𝔸[K] (σ x)) ∧
    ∀ g : G1 K n, ((θ.e g : G1 K n) : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map s.toRingHom (g : AdelicGLn.AdelicGL K n)

def Stable {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (D : TypeDat K n) (θ : Twist μ) : Prop :=
  (∀ k, θ.e k ∈ D.U ↔ k ∈ D.U) ∧ ∀ k ∈ D.U, D.e (θ.e k) = D.e k

structure Pair (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) : Prop where
  irr₁ : CuspIrr μ₂ τ₁
  irr₂ : CuspIrr μ₂ τ₂
  orth : τ₁ ⟂ τ₂

def HPSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a b : ℕ), 0 < a → 0 < b →
    Continuous (HP (K := K) a b) ∧
    (∀ g : G1 K (a + b), ∃ (X : UPos (a + b) a → 𝔸[K]) (m₁ : AdelicGLn.AdelicGL K a) (m₂ : AdelicGLn.AdelicGL K b),
      ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (a + b))), (g : AdelicGLn.AdelicGL K (a + b)) = unipGL X * blk m₁ m₂ * k) ∧
    (∀ (g : G1 K (a + b)) (X : UPos (a + b) a → 𝔸[K]) (m₁ : AdelicGLn.AdelicGL K a) (m₂ : AdelicGLn.AdelicGL K b),
      ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (a + b))), (g : AdelicGLn.AdelicGL K (a + b)) = unipGL X * blk m₁ m₂ * k →
        HP a b g = Real.log (detModule K a m₁).1) ∧
    (∀ (g : G1 K (a + b)) (T : ℝ), {q : Quotient (QuotientGroup.rightRel (ParΓ K a b)) |
      T ≤ HP a b ((q.out : G1 K (a + b)) * g)}.Finite) ∧
    ∃ c C : ℝ, 0 < c ∧ ∀ g : G1 K (a + b), HP a b g ≤ c * Real.log (qht g) + C

def LineEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ D : TypeDat K (2 + 2), ∃ d, Nonempty (Line μ τ₁ τ₂ D d)

section Steps

variable (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
  {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')

def ShiftCausal (T₀ : ℝ) : Prop :=
  (∀ (t : ℝ) (u u' : L (Eu d)) (v v' : L (Eu d')), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
    ⟪A.J u', A'.J v⟫_ℂ = ⟪A.J u, A'.J v'⟫_ℂ) ∧
  ∀ (s : ℝ) (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * T₀ - s → v x = 0) →
    ⟪A.J u, A'.J v⟫_ℂ = 0

def ActsBy (f : CC K (2 + 2)) (β : ℝ → Eu d →L[ℂ] Eu d) : Prop :=
  Ker β ∧ Conv A.J A.J (Rop μ f) β ∧
    ∀ (z : ℂ) (v : Eu d) (x : G1 K (2 + 2)), ∫ g, f g * flat z (A.sec v) (x * g) ∂μ = flat z (A.sec (symb β z v)) x

def ScalarAt : Prop :=
  ∃ (a : CC K (2 + 2)) (b : ℝ → ℂ), Smooth a ∧ D.Hecke a ∧ CuspidalProjection.ccStar a = a ∧ Continuous b ∧ HasCompactSupport b ∧
    ∫ t, b t ≠ 0 ∧ Conv A.J A.J (Rop μ a) (fun t => b t • ContinuousLinearMap.id ℂ (Eu d)) ∧
    Conv A'.J A'.J (Rop μ a) fun t => b (-t) • ContinuousLinearMap.id ℂ (Eu d')

def Family (T₀ : ℝ) (P : L2 μ →L[ℂ] L2 μ) (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (C : ℝ) : Prop :=
  (∀ (f : CC K (2 + 2)) β β', ActsBy μ A f β → ActsBy μ A' f β' → ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
  ∀ (X Λ : L2 μ →L[ℂ] L2 μ) (κ : ℝ → Eu d →L[ℂ] Eu d') (T B : ℝ), Ker κ → Conv A.J A'.J X κ → X ∘L P = P ∘L X → T₀ ≤ T →
    IsTrunc A.J A'.J T Λ → IsTraceClass (Λ ∘L X ∘L P ∘L Λ) → (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ B / (1 + |z.im|)) →
    ‖trace (Λ ∘L X ∘L P ∘L Λ) -
        (1 / 2 : ℂ) * LinearMap.trace ℂ (Eu d) ((N.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d) ∘ₗ (symb κ 0 : Eu d →ₗ[ℂ] Eu d'))‖ ≤
      C * B * Real.exp (-2 * T)

end Steps

def ForAll (p : ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) (d d' : ℕ), Line μ τ₁ τ₂ D d → Line μ τ₂ τ₁ D d' → Prop) :
    Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ (D : TypeDat K (2 + 2)) (d d' : ℕ)
    (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), p K μ μ₂ τ₁ τ₂ D d d' A A'

def PairFacts : Prop := ForAll fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => ShiftCausal μ A A' 0

def CtZero : Prop := ForAll fun _ _ _ μ _ _ _ _ _ D _ _ A _ =>
  ∀ u, Pc μ (A.J u) = 0 ∧ D.FixedByTypeProjector μ (A.J u) ∧ constantTermL2 μ 1 (A.J u) =ᵐ[μ] 0 ∧ constantTermL2 μ 3 (A.J u) =ᵐ[μ] 0

def ConvR : Prop := ForAll fun K _ _ μ _ _ _ _ _ D _ _ A _ => ∀ f : CC K (2 + 2), D.Hecke f → ∃ β, ActsBy μ A f β

def ConvU : Prop := ForAll fun K _ _ μ _ μ₂ _ τ₁ τ₂ D d d' A A' =>
  ∀ (σ : K ≃+* K) (θ : Twist μ) (θ₂ : Twist μ₂), IsGal σ θ → IsGal σ θ₂ → Stable D θ →
    τ₁.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₂ → τ₂.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₁ →
    ∃ s : Eu d ≃ₗᵢ[ℂ] Eu d', (∀ v x, A'.sec (s v) x = A.sec v (θ.e.symm x)) ∧
      ∀ (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, v x = s (u x)) → θ.U (A.J u) = A'.J v

def TruncHS : Prop := ForAll fun K _ _ μ _ _ _ _ _ D _ _ A A' =>
  ∀ (a : CC K (2 + 2)) (P Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), Smooth a → D.Hecke a → IsOrthogonalProjectionTwoLines A.J A'.J P → 0 ≤ T →
    IsTrunc A.J A'.J T Λ → IsHilbertSchmidt (Λ ∘L Rop μ a ∘L P)

def KernEx : Prop := ForAll fun K _ _ μ _ _ _ _ _ D _ _ A A' =>
  ∀ (θ : Twist μ) (a g : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → θ.U ∘L P = P ∘L θ.U →
    (∀ (T : ℝ) (Λ : L2 μ →L[ℂ] L2 μ), 0 ≤ T → IsTrunc A.J A'.J T Λ → θ.U ∘L Λ = Λ ∘L θ.U) →
    Smooth a → D.Hecke a → Smooth (CuspidalProjection.ccStar g) → D.Hecke g →
    ∃ c : ℝ, 0 < c ∧ ∀ N' : ℕ, ∃ (C T₁ : ℝ) (N : ℕ), ∀ (f : CC K (2 + 2)) (M Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), T₁ ≤ T →
      M ∘L Pc μ = Pc μ ∘L M → M ∘L P = P ∘L M → Rop μ f = Rop μ a ∘L M ∘L Rop μ g → IsTrunc A.J A'.J T Λ →
      (∀ x : G1 K (2 + 2), Real.exp (c * T) < qht x → twK θ f x = 0) →
      IsTraceClass (Λ ∘L (Rop μ f ∘L θ.U) ∘L P ∘L Λ) ∧
      ‖twInt θ f - cuspTr μ θ f - trace (Λ ∘L (Rop μ f ∘L θ.U) ∘L P ∘L Λ)‖ ≤
        C * Real.exp (N * T) * ‖M ∘L (ContinuousLinearMap.id ℂ (L2 μ) - Pc μ - P)‖ + C * Real.exp (-(N' * T)) * ‖M‖

def Complete : Prop := ForAll fun K _ _ μ _ μ₂ _ τ₁ τ₂ D _ _ A A' =>
  ∀ (P : L2 μ →L[ℂ] L2 μ) (w : L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → D.FixedByTypeProjector μ w → Pc μ w = 0 →
    constantTermL2 μ 1 w =ᵐ[μ] 0 → constantTermL2 μ 3 w =ᵐ[μ] 0 →
    (∀ ρ₁ ρ₂ : Submodule ℂ (L2 μ₂), CuspIrr μ₂ ρ₁ → CuspIrr μ₂ ρ₂ → ¬ (ρ₁ = τ₁ ∧ ρ₂ = τ₂) → ¬ (ρ₁ = τ₂ ∧ ρ₂ = τ₁) →
      ∀ (f : G1 K (2 + 2) → ℂ) (β : ℝ → ℂ) (φ : L2 μ), IsSec ρ₁ ρ₂ f → Continuous β → HasCompactSupport β →
        Reps μ φ (theta β f) → ⟪φ, w⟫_ℂ = 0) → P w = w

def ScalarB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
    ∀ (σ : K ≃+* K) (θ : Twist μ) (θ₂ : Twist μ₂), (∀ x, σ (σ x) = x) → IsGal σ θ → IsGal σ θ₂ →
      τ₁.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₂ → τ₂.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₁ →
      (∀ w : InfinitePlace K, w.comap σ.toRingHom ≠ w) →
    ∀ Kf : Subgroup (AdelicGLn.FiniteAdelicGL K (2 + 2)), IsOpen (Kf : Set (AdelicGLn.FiniteAdelicGL K (2 + 2))) →
      Kf ≤ AdelicGLn.integralFiniteGL K (2 + 2) →
      (∀ k : G1 K (2 + 2), (AdelicGLn.prodEquiv K (2 + 2) (θ.e k)).2 ∈ Kf ↔ (AdelicGLn.prodEquiv K (2 + 2) k).2 ∈ Kf) →
    ∃ D : TypeDat K (2 + 2), D.Level Kf ∧ Stable D θ ∧
      ((∃ f, f ≠ 0 ∧ IsSec τ₁ τ₂ f ∧ ∀ k : G1 K (2 + 2), (AdelicGLn.prodEquiv K (2 + 2) k).1 = 1 →
          (AdelicGLn.prodEquiv K (2 + 2) k).2 ∈ Kf → ∀ g, f (g * k) = f g) → ∃ f, f ≠ 0 ∧ IsSec τ₁ τ₂ f ∧ D.Fix f) ∧
      ∀ (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), ScalarAt μ A A'

def ProjEx : Prop := ForAll fun _ _ _ μ _ _ _ _ _ _ _ _ A A' =>
  ShiftCausal μ A A' 0 → (∃ P, IsOrthogonalProjectionTwoLines A.J A'.J P) ∧ ∀ T : ℝ, 0 ≤ T → ∃ Λ, IsTrunc A.J A'.J T Λ

def FamilyOf : Prop := IntegralApplyAeEq.Main → PairFacts → TruncHS → ForAll fun _ _ _ μ _ _ _ _ _ _ _ _ A A' =>
  ScalarAt μ A A' → ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → ∃ N C, Family μ A A' 0 P N C

def TypeEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ D : TypeDat K n, D.Level (AdelicGLn.integralFiniteGL K n) ∧ ∀ k, D.e k = 1

end PositivityTheory.Rg.Tf.Adel
