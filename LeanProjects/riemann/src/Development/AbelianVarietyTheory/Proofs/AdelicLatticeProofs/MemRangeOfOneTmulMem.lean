import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties

namespace GlobalTheory.AdIdem

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct nonZeroDivisors

section

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_integral (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  have hy : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, hm, h⟩ := hy.exists_integral_multiple
  refine ⟨(m * m).toNat, ?_, ?_⟩
  · have := mul_self_pos.2 hm
    omega
  · have h2 : (((m * m).toNat : ℕ) : E) = (m : E) * m := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (mul_self_nonneg m), Int.cast_mul]
    have h3 : IsIntegral ℤ ((m : E) * (m • y)) :=
      IsIntegral.mul (by simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := m)) h
    refine ⟨⟨_, h3⟩, ?_⟩
    rw [h2, mul_assoc, ← zsmul_eq_mul y m]
    rfl

omit [NumberField E] in
theorem mul_mem_hat {x y : RA F E} (hx : x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hy : y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x * y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  refine mul_mem_adelicCompletionOfElementSet_of_mul_mem F ?_ hx hy
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨a * b, map_mul _ _ _⟩

theorem exists_eq_one_tmul_add (z : RA F E) :
    ∃ (x : E), ∃ h ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x + h := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a y =>
    obtain ⟨d, hd, hy⟩ := exists_nat_mul_integral E y
    obtain ⟨x, b, hb, rfl⟩ := exists_eq_algebraMap_add_nsmul F d hd a
    refine ⟨x • y, b ⊗ₜ[F] ((d : E) * y), tmul_mem_adelicCompletion_of_integral F hb hy, ?_⟩
    rw [TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  | add u v hu hv =>
    obtain ⟨x, h, hh, rfl⟩ := hu
    obtain ⟨x', h', hh', rfl⟩ := hv
    refine ⟨x + x', h + h', add_mem hh hh', ?_⟩
    rw [TensorProduct.tmul_add]
    abel

theorem mem_range_of_one_tmul_mem {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext y
    exact FractionalIdeal.mem_one_iff _
  rw [← h] at hx ⊢
  exact (one_tmul_mem_adelicCompletion_fractionalIdeal_iff F 1 x).1 hx

theorem mem_hat_of_idempotent (z : RA F E) (hz : z * z = z) :
    z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨x, h, hh, hx⟩ := exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hNx⟩ := exists_nat_mul_integral E x
  have h1 : (1 : RA F E) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
    one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  have hc : ∀ y : E, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E) * y) =
      N • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y : RA F E) := by
    intro y
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul]
  have hNz : N • z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    rw [hx, nsmul_add, ← hc]
    exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F hNx) (nsmul_mem hh N)
  have hpow : ∀ n : ℕ, ∃ a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      ∃ b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (z - h) ^ n = a + z * b := by
    intro n
    induction n with
    | zero => exact ⟨1, h1, 0, zero_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha, b, hb, e⟩ := ih
      refine ⟨-(a * h), neg_mem (mul_mem_hat F E ha hh), a + b - b * h,
        sub_mem (add_mem ha hb) (mul_mem_hat F E hb hh), ?_⟩
      rw [pow_succ, e]
      linear_combination b * hz
  have hzh : z - h = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by rw [hx]; abel
  have hint : ∀ n : ℕ, (N : E) * x ^ n ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro n
    apply mem_range_of_one_tmul_mem F E
    obtain ⟨a, ha, b, hb, e⟩ := hpow n
    rw [hzh, Algebra.TensorProduct.tmul_pow, one_pow] at e
    rw [hc, e, nsmul_add, ← smul_mul_assoc]
    exact add_mem (nsmul_mem ha N) (mul_mem_hat F E hNz hb)
  have hai : IsAlmostIntegral (𝓞 E) x := by
    refine ⟨(N : 𝓞 E), mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hN.ne'), fun n => ?_⟩
    rw [Algebra.smul_def, map_natCast]
    exact hint n
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hai.isIntegral
  rw [hx]
  exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F ⟨r, hr⟩) hh

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idempotent_mem_intAE : ∀ (D : D7) (z : Af D.host.F ⊗[D.host.F] D.host.E), z * z = z → z ∈ intAE D := by
  intro D z hz
  have h : intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
    unfold intAE GlobalTheory.AdLat.hat1
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, rfl⟩
      exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
      exact ⟨a, ha, x, rfl⟩
  rw [h]
  exact mem_hat_of_idempotent D.host.F D.host.E z hz

end

end GlobalTheory.AdIdem
