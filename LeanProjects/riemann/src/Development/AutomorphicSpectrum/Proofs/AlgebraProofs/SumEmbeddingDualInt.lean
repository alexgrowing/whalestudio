import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.EigDim

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_eigProj [FiniteDimensional K V] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (eigProj ρ σ) = (finrank K (eigSp ρ σ) : K) :=
  LinearMap.IsProj.trace (p := eigSp ρ σ)
    ⟨fun x => eigProj_mem ρ σ x, fun _ hx => eigProj_of_mem hx⟩

theorem sum_embedding_dualInt [IsAlgClosed K] [CharZero K]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∑ σ : E →+* K, σ (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : K) := by
  have h1 : ∑ σ : E →+* K, σ (dualInt E k) = ∑ σ : E →ₐ[ℚ] K, σ (dualInt E k) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E K) _ _ fun _ => rfl
  have h2 := repr_eq_trace (E := E) 1 k
  rw [h1, ← trace_eq_sum_embeddings (E := K) (K := ℚ) (L := E)]
  have h3 : ((1 : 𝓞 E) : E) = 1 := map_one (algebraMap (𝓞 E) E)
  rw [h3, mul_one] at h2
  rw [← h2]
  simp

theorem sum_eigProj [IsAlgClosed K] [CharZero K] (ρ : 𝓞 E →+* Module.End K V) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  unfold eigProj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_embedding_dualInt]
  conv_rhs => rw [← map_one ρ, ← (RingOfIntegers.basis E).sum_repr 1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem finrank_eigSp_mul :
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V),
      (∀ a : 𝓞 E, ∃ n : ℤ, LinearMap.trace K V (ρ a) = (n : K)) →
      ∀ σ : E →+* K, Module.finrank K (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) * Module.finrank ℚ E =
        Module.finrank K V := by
  intro K _ _ _ V _ _ _ E _ _ ρ htr σ
  choose m hm using fun k => htr (RingOfIntegers.basis E k)
  set l : E := ∑ k, (m k : E) * dualInt E k with hl
  have h1 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : K) = τ l := by
    intro τ
    rw [← trace_eigProj, hl, map_sum]
    unfold eigProj
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hm, map_mul, map_intCast, smul_eq_mul, mul_comm]
  have h2 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : E) = l := fun τ =>
    τ.injective (by rw [map_natCast, h1])
  have h3 : ∀ τ : E →+* K, finrank K (eigSp ρ τ) = finrank K (eigSp ρ σ) := fun τ =>
    Nat.cast_injective ((h2 τ).trans (h2 σ).symm)
  have h4 : (finrank K V : K) = ∑ τ : E →+* K, (finrank K (eigSp ρ τ) : K) := by
    rw [← LinearMap.trace_one, ← sum_eigProj ρ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => trace_eigProj ρ τ
  simp_rw [h3] at h4
  rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul] at h4
  have h5 : finrank K V = finrank ℚ E * finrank K (eigSp ρ σ) := by exact_mod_cast h4
  rw [h5, mul_comm]

end GlobalTheory.CompanionTheory.Ar.HT.EigDim
