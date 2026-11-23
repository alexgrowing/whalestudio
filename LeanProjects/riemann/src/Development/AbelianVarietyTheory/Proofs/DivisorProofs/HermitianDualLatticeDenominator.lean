import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.TraceDenom

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  have h : ∀ i, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    have hal : IsAlgebraic ℤ (f i) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (f i))
    obtain ⟨y, hy0, hy⟩ := hal.exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
        rw [← Int.cast_natCast]; congr 1; omega
      rw [e, ← zsmul_eq_mul]; exact hy
    · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
        rw [← Int.cast_natCast, ← Int.cast_neg]; congr 1; omega
      rw [e, neg_mul, ← zsmul_eq_mul]; exact hy.neg
  choose m hm0 hm using h
  refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm0 i), fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  rw [hk, Nat.cast_mul, mul_comm ((m i : ℕ) : E), mul_assoc]
  have hk' : IsIntegral ℤ ((k : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ)))
  exact hk'.mul (hm i)

theorem exists_preimage_ringOfIntegers {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (b : 𝓞 E) : ∃ a : 𝓞 E, σ (a : E) = b := by
  obtain ⟨x, hx⟩ := σ.bijective.2 (b : E)
  have h1 : IsIntegral ℤ (σ.toRingHom.toIntAlgHom x) := by
    change IsIntegral ℤ (σ x); rw [hx]; exact b.isIntegral_coe
  have hint : IsIntegral ℤ x :=
    (isIntegral_algHom_iff (σ.toRingHom.toIntAlgHom) σ.injective).1 h1
  exact ⟨⟨x, hint⟩, hx⟩

theorem nat_mul_integral_of_trace_form_int : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (c : E) (hc : c ≠ 0),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : Fin n → E, (∀ β : Fin n → 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (c * form σ J ξ (fun i => (β i : E))) = z) →
      ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
  intro F E _ _ _ _ _ σ n J hJ c hc
  obtain ⟨D, hD, hDual⟩ := GlobalTheory.exists_den_traceDual_ringOfIntegers (F := E)
  obtain ⟨M, hM, hMint⟩ := exists_nat_mul_isIntegral (fun p : Fin n × Fin n => c⁻¹ * J⁻¹ p.1 p.2)
  refine ⟨D * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD.ne' hM.ne'), fun ξ hξ i => ?_⟩
  have hv : ∀ k, ∃ o : 𝓞 E, (D : E) * (c * (ξ ᵥ* J) k) = o := by
    intro k
    apply hDual
    intro b
    obtain ⟨a, ha⟩ := exists_preimage_ringOfIntegers σ b
    obtain ⟨z, hz⟩ := hξ (Pi.single k a)
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    have hs : (fun j => σ (((Pi.single k a : Fin n → 𝓞 E) j : E))) = Pi.single k (σ (a : E)) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    simp only [form, Matrix.dotProduct_mulVec, hs]
    simp [dotProduct, Pi.single_apply, ha, mul_assoc]
  choose o ho using hv
  have hunit : IsUnit J.det := hJ.isUnit
  have hξeq : ξ = (ξ ᵥ* J) ᵥ* J⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hunit, Matrix.vecMul_one]
  generalize ξ ᵥ* J = v at ho hξeq
  have hexp : ((D * M : ℕ) : E) * ξ i =
      ∑ k, (D : E) * (c * v k) * ((M : E) * (c⁻¹ * J⁻¹ k i)) := by
    rw [hξeq]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    field_simp
  have hint : IsIntegral ℤ (((D * M : ℕ) : E) * ξ i) := by
    rw [hexp]
    refine IsIntegral.sum _ fun k _ => ?_
    rw [ho k]
    exact (o k).isIntegral_coe.mul (hMint (k, i))
  exact ⟨⟨_, hint⟩, rfl⟩

end GlobalTheory.TraceDenom
