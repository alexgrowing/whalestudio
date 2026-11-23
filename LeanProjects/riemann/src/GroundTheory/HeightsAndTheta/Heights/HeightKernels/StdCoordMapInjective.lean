import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardInnerSingleNe
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.LineCoordinates.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    ∃ (n : ℕ) (e : Fin n ≃ X) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ)
      (ψ : E.carrier →ₗ[𝓞 K] (Fin n → K)),
      (∀ i, a i ≠ 0) ∧ (∀ σ i, 0 < d σ i) ∧ (∀ σ i, d (conjugate σ) i = d σ i) ∧
      Function.Injective ψ ∧ LinearMap.range ψ = idealLattice a ∧
      Module.finrank (𝓞 K) E.carrier = n ∧
      (∀ i, (L (e i)).map ψ = idealLattice a ⊓
        (Submodule.span K {(Pi.single i 1 : Fin n → K)}).restrictScalars (𝓞 K)) ∧
      ∀ (σ : K →+* ℂ) (v w : E.carrier),
        (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
          star (embVec σ (ψ v)) ⬝ᵥ (diagMetric d σ *ᵥ embVec σ (ψ w))

def S6.CoordinateDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (n : ℕ)
    (H : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (ψ : E.carrier →ₗ[𝓞 K] (Fin n → K)),
    Function.Injective ψ → Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ →
    (∀ (σ : K →+* ℂ) (v w : E.carrier),
        (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
          star (embVec σ (ψ v)) ⬝ᵥ (H σ *ᵥ embVec σ (ψ w))) →
    ∀ (G : Submodule (𝓞 K) E.carrier) (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K),
      LinearIndependent K u →
      G.map ψ = LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) →
      E.degree G = subDegree (LinearMap.range ψ) H u

def S6.QuotientDegreeSplit.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K))
    (H : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), Λ.FG →
    Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
      LinearIndependent K (Sum.elim b c) → m + k = n →
      quotDegree Λ H b c = subDegree Λ H (Sum.elim b c) - subDegree Λ H b

def S6.ExtensionDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E' E E'' : HermitianBundle.{0} K)
    (Y : HermitianExtension E' E E''),
    E''.degree ⊤ = E.degree ⊤ - E.degree (LinearMap.range Y.incl)

def S6.SaturatedSpan.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] (n : ℕ) (ψ : M →ₗ[𝓞 K] (Fin n → K)), Function.Injective ψ →
    ∀ G : Submodule (𝓞 K) M, (∀ (t : 𝓞 K) (x : M), t ≠ 0 → t • x ∈ G → x ∈ G) →
      ∃ b : Fin (Module.finrank (𝓞 K) G) → Fin n → K, LinearIndependent K b ∧
        G.map ψ = LinearMap.range ψ ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)

def stdCoordMap (K : Type*) [Field K] (n : ℕ) : (Fin n → 𝓞 K) →ₗ[𝓞 K] (Fin n → K) :=
  LinearMap.pi fun i => (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj i)

theorem stdCoordMap_apply (K : Type*) [Field K] (n : ℕ) (v : Fin n → 𝓞 K) (i : Fin n) :
    stdCoordMap K n v i = (v i : K) := rfl

theorem stdCoordMap_injective (K : Type*) [Field K] (n : ℕ) :
    Function.Injective (stdCoordMap K n) := by
  intro v w h
  funext i
  exact Subtype.ext (congrFun h i)

theorem stdCoordMap_single (K : Type*) [Field K] (n : ℕ) (i : Fin n) :
    stdCoordMap K n (Pi.single i 1) = Pi.single i 1 := by
  funext j
  rw [stdCoordMap_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem stdCoordMap_span (K : Type*) [Field K] (n : ℕ) :
    Submodule.span K (LinearMap.range (stdCoordMap K n) : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine Submodule.subset_span ⟨Pi.single i 1, ?_⟩
  rw [stdCoordMap_single, Pi.basisFun_apply]

theorem stdCoordMap_inner (K : Type*) [Field K] [NumberField K] (n : ℕ) (σ : K →+* ℂ)
    (v w : Fin n → 𝓞 K) :
    ((HermitianBundle.standard K n).metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
      star (embVec σ (stdCoordMap K n v)) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ
        embVec σ (stdCoordMap K n w)) := by
  refine (HermitianMetric.standard_inner K (Fin n) σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v)
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w)).trans ?_
  rw [Matrix.one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [standardCoord_tmul, standardCoord_tmul]
  simp [embVec, stdCoordMap_apply, ComplexAt.ofComplex]

theorem S6.LineCoordinates.hypotheses_inhabited :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) :=
  ⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ⟩

theorem S6.CoordinateDegree.hypotheses_inhabited :
    Function.Injective (stdCoordMap ℚ 2) ∧
      Submodule.span ℚ (LinearMap.range (stdCoordMap ℚ 2) : Set (Fin 2 → ℚ)) = ⊤ ∧
      (∀ (σ : ℚ →+* ℂ) (v w : Fin 2 → 𝓞 ℚ),
        ((HermitianBundle.standard ℚ 2).metric.form σ).inner
            ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] w) =
          star (embVec σ (stdCoordMap ℚ 2 v)) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
            embVec σ (stdCoordMap ℚ 2 w))) ∧
      LinearIndependent ℚ (Pi.basisFun ℚ (Fin 2)) ∧
      (⊤ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)).map (stdCoordMap ℚ 2) =
        LinearMap.range (stdCoordMap ℚ 2) ⊓
          (Submodule.span ℚ (Set.range (Pi.basisFun ℚ (Fin 2)))).restrictScalars (𝓞 ℚ) := by
  refine ⟨stdCoordMap_injective ℚ 2, stdCoordMap_span ℚ 2, stdCoordMap_inner ℚ 2,
    (Pi.basisFun ℚ (Fin 2)).linearIndependent, ?_⟩
  rw [(Pi.basisFun ℚ (Fin 2)).span_eq, Submodule.restrictScalars_top, inf_top_eq,
    Submodule.map_top]

theorem S6.QuotientDegreeSplit.hypotheses_inhabited :
    (idealLattice (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ))).FG ∧
      Submodule.span ℚ (idealLattice (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) :
        Set (Fin 2 → ℚ)) = ⊤ ∧
      LinearIndependent ℚ (Sum.elim
        (fun i : Fin 1 => (Pi.single (Fin.castAdd 1 i) 1 : Fin (1 + 1) → ℚ))
        fun j : Fin 1 => (Pi.single (Fin.natAdd 1 j) 1 : Fin (1 + 1) → ℚ)) ∧ 1 + 1 = 2 := by
  obtain ⟨hFG, hspan⟩ := LinesIdealLatticeFG.full ℚ 2 _ fun _ => one_ne_zero
  refine ⟨hFG, hspan, ?_, rfl⟩
  have h := (stdSumBasis ℚ 1 1).linearIndependent
  rw [← stdSumBasis_elim] at h
  simpa only [stdSumBasis_inl, stdSumBasis_inr] using h

theorem S6.ExtensionDegree.hypotheses_inhabited :
    Nonempty (HermitianExtension (HermitianBundle.integers ℚ) (HermitianBundle.standard ℚ 2)
      (HermitianBundle.integers ℚ)) :=
  ⟨HermitianExtension.standardSplit ℚ⟩

theorem S6.SaturatedSpan.hypotheses_inhabited :
    Function.Injective (stdCoordMap ℚ 2) ∧
      ∀ (t : 𝓞 ℚ) (x : Fin 2 → 𝓞 ℚ), t ≠ 0 → t • x ∈ LinearMap.range (firstIncl ℚ) →
        x ∈ LinearMap.range (firstIncl ℚ) :=
  ⟨stdCoordMap_injective ℚ 2, fun t x ht hx =>
    standardFlag_saturated (K := ℚ) 1 t x ht hx⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
