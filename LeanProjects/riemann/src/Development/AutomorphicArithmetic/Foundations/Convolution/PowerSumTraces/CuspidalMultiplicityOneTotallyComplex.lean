import Mathlib
import GroundTheory.AutomorphicForms.TraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import GroundTheory.AutomorphicForms.GKModules.Casimir

noncomputable section

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.ConvolutionTheory.C

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def prj (V : Submodule ℂ H) : H →L[ℂ] H := V.topologicalClosure.starProjection

def trOn (V : Submodule ℂ H) (T : H →L[ℂ] H) : ℂ := trace (prj V ∘L T ∘L prj V)

def eigIn (W : Submodule ℂ H) (A : H →L[ℂ] H) (x : ℝ) : Submodule ℂ H :=
  W ⊓ Module.End.eigenspace (A : H →ₗ[ℂ] H) (x : ℂ)

variable {G : Type*} [Group G] [TopologicalSpace G]

structure IsSummandOf (π : UnitaryRep G H) (W V : Submodule ℂ H) : Prop where
  le : V ≤ W
  closed : IsClosed (V : Set H)
  inv : π.IsInvariant V
  ne_bot : V ≠ ⊥
  irred : ∀ V' ≤ V, IsClosed (V' : Set H) → π.IsInvariant V' → V' = ⊥ ∨ V' = V

end Hilbert

section Global

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

abbrev LL (μ : Measure (normOneGL K n)) : Type _ := Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def IsSummand (V : Submodule ℂ (LL μ)) : Prop :=
  IsSummandOf (rightRegularRep (rationalGLOne K n) μ) (cuspidalL2 μ) V

def MultOneAt : Prop := ∀ V V' : Submodule ℂ (LL μ), IsSummand μ V → IsSummand μ V' → V ≠ V' → V ⟂ V'

abbrev RR (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) : LL μ →L[ℂ] LL μ :=
  (rightRegularRep (rationalGLOne K n) μ).integrated μ (UnitaryRep.ccToL1 μ f)

def IsLeftSmooth (a : normOneGL K n → ℂ) : Prop :=
  (∀ x, (isExpLieAlgebra K n).IsSmoothFun fun A : archGroup K n => a (archP K n A * x)) ∧
    ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
      ∀ u ∈ U, ∀ x, a (finOne K n u * x) = a x

variable (K n) in

def trForm (X Y : (isExpLieAlgebra K n).lieSubalgebra) : ℝ :=
  Algebra.trace ℝ _ (Matrix.trace ((X : ArchMatrix K n) * (Y : ArchMatrix K n)))

end Global

def CuspidalMultiplicityOneTotallyComplex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure],
    MultOneAt μ

def TraceSum : Prop :=
  ∀ (H ι : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (V : ι → Submodule ℂ H)
    (T : H →L[ℂ] H), (Pairwise fun i j => V i ⟂ V j) → IsTraceClass (prj (⨆ i, V i) ∘L T ∘L prj (⨆ i, V i)) →
    HasSum (fun i => trOn (V i) T) (trOn (⨆ i, V i) T)

def SummandsSpan : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure],
    (⨆ V : {V // IsSummand μ V}, V.1).topologicalClosure = cuspidalL2 μ

def TwistedSum : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G ≃* G) (U : H ≃ₗᵢ[ℂ] H) (B : H →L[ℂ] H),
    (∀ g v, U (π g v) = π (e g) (U v)) → W.map (U : H →ₗ[ℂ] H) = W →
    (⨆ V : {V // IsSummandOf π W V}, V.1).topologicalClosure = W →
    (∀ V V', IsSummandOf π W V → IsSummandOf π W V' → V ≠ V' → V ⟂ V') →
    (∀ V, IsSummandOf π W V → ∀ v ∈ V, B v ∈ V) → IsTraceClass (prj W ∘L B ∘L prj W) →
    HasSum (fun V : {V // IsSummandOf π W V ∧ V.map (U : H →ₗ[ℂ] H) = V} => trOn V.1 (B ∘L (U : H →L[ℂ] H)))
      (trOn W (B ∘L (U : H →L[ℂ] H)))

def EigSplit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H),
    IsClosed (W : Set H) → 0 ≤ A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∀ η : ℝ, 0 < η →
    ∃ S : Finset ℝ, (∀ x, x ∈ S ↔ η < x ∧ eigIn W A x ≠ ⊥) ∧ (∀ x ∈ S, FiniteDimensional ℂ (eigIn W A x)) ∧
      ∀ (φ : ℝ → ℝ) (c : ℝ) (T : H →L[ℂ] H), Continuous φ → 0 ≤ c → (∀ x ∈ Set.Icc 0 η, |φ x| ≤ c) →
        IsTraceClass (prj W ∘L T ∘L prj W) →
        ‖trOn W (cfc φ A ∘L prj W ∘L T) - ∑ x ∈ S, (φ x : ℂ) * trOn (eigIn W A x) T‖ ≤
          c * (traceNorm (prj W ∘L T ∘L prj W)).toReal

def EigSummands : Prop :=
  ∀ (H ι : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (V : ι → Submodule ℂ H)
    (W : Submodule ℂ H) (A : H →L[ℂ] H) (x : ℝ), (∀ i, IsClosed (V i : Set H)) → (Pairwise fun i j => V i ⟂ V j) →
    (⨆ i, V i).topologicalClosure = W → IsSelfAdjoint A → (∀ i, ∀ v ∈ V i, A v ∈ V i) →
    FiniteDimensional ℂ (eigIn W A x) →
    ∃ s : Finset ι, (∀ i, i ∈ s ↔ eigIn (V i) A x ≠ ⊥) ∧ eigIn W A x = ⨆ i ∈ s, eigIn (V i) A x ∧
      ∀ T : H →L[ℂ] H, trOn (eigIn W A x) T = ∑ i ∈ s, trOn (eigIn (V i) A x) T

def OpBasics : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ),
    (∀ V, IsSummand μ V → ∀ v ∈ V, RR μ f v ∈ V) ∧ (∀ v ∈ cuspidalL2 μ, RR μ f v ∈ cuspidalL2 μ) ∧
      IsCompactOperator (RR μ f ∘L prj (cuspidalL2 μ))

def NearFinite : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : ι → ℝ), (∀ i, ε i * ε i = 1) →
    (∀ i j, trForm K n (b i) (b j) = if i = j then ε i else 0) →
    ∀ (U : Subgroup (AdelicGLn.integralFiniteGL K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (τ : Representation ℂ (archCompact K n) X) (c : ℝ),
      FiniteDimensional ℂ (Submodule.span ℂ {φ : cuspForms K n | φ ∈ centralCuspForms K n ∧
        (∀ u ∈ U, ∀ g, φ.1 (g * finEmb K n (u : AdelicGLn.integralFiniteGL K n)) = φ.1 g) ∧
        (∃ f : X →ₗ[ℂ] cuspForms K n, (∀ k x g, (f (τ k x)).1 g = (f x).1 (g * infEmb K n (k : archGroup K n))) ∧
          φ ∈ LinearMap.range f) ∧
        ∃ (h : φ.1 ∈ archSmooth K n) (κ : ℂ), -c ≤ κ.re ∧ uAction (casimir b ε) ⟨φ.1, h⟩ = κ • ⟨φ.1, h⟩})

end UpperTheory.ConvolutionTheory.C
