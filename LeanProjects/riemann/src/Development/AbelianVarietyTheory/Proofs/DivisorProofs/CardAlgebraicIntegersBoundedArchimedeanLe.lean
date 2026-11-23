import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory.IntCount

theorem exists_abs_repr_le_mul_house (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem card_bounded_integers_le (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧
      ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  classical
  obtain ⟨c, hc, hb⟩ := exists_abs_repr_le_mul_house E
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  refine ⟨Fintype.card ι, (2 * c + 3) ^ Fintype.card ι, by positivity, fun T hT => ?_⟩
  set S := {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T} with hS
  let M : ℕ := ⌈c * T⌉₊
  let s : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  let f : 𝓞 E → (ι → ℤ) := fun ξ j => (RingOfIntegers.basis E).repr ξ j
  have hf : Function.Injective f := fun ξ η h =>
    (RingOfIntegers.basis E).ext_elem fun j => congrFun h j
  have hmaps : ∀ ξ ∈ S, f ξ ∈ s := by
    intro ξ hξ
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 (abs_le.1 ?_)
    have hh : house (ξ : E) ≤ T := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun φ => ?_
      have := hξ (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h1 := hb ξ j
    have h2 : c * house (ξ : E) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_left hh hc).trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hsub : S ⊆ f ⁻¹' (s : Set (ι → ℤ)) := fun ξ hξ => hmaps ξ hξ
  have hfin : S.Finite := ((s.finite_toSet).preimage hf.injOn).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ s.card := by
    rw [← Set.ncard_coe_finset s]
    exact Set.ncard_le_ncard_of_injOn f (fun ξ hξ => hmaps ξ hξ) hf.injOn s.finite_toSet
  have hs : (s.card : ℝ) = (2 * (M : ℝ) + 1) ^ Fintype.card ι := by
    simp only [s, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    push_cast
    congr 1
    have : (↑M + 1 - -↑M : ℤ).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hM : (M : ℝ) ≤ c * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbase : 2 * (M : ℝ) + 1 ≤ (2 * c + 3) * T := by nlinarith
  calc (S.ncard : ℝ) ≤ s.card := by exact_mod_cast hcard
    _ = (2 * (M : ℝ) + 1) ^ Fintype.card ι := hs
    _ ≤ ((2 * c + 3) * T) ^ Fintype.card ι := by gcongr
    _ = (2 * c + 3) ^ Fintype.card ι * T ^ Fintype.card ι := mul_pow _ _ _

end GlobalTheory.IntCount
