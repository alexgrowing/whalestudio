import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem absNorm_pow_eq_prod_sq {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (v : HeightOneSpectrum (𝓞 L)) (h : ℕ)
    (k : L) (hk : FractionalIdeal.spanSingleton (𝓞 L)⁰ k = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ h = (∏ i, ‖φ i k‖) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm k
  rw [← hφ.prod_comp] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) k ^ (InfinitePlace.mk (φ i)).mult = ‖φ i k‖ ^ 2 := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  simp_rw [h2] at h1
  have h3 := congrArg FractionalIdeal.absNorm hk
  rw [FractionalIdeal.absNorm_span_singleton, map_pow, FractionalIdeal.coeIdeal_absNorm] at h3
  rw [← Finset.prod_pow, h1, h3]
  simp

theorem valTw_mem_kummerField : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [IsTotallyComplex L] (φ₀ : L →+* ℂ) (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∀ (v : HeightOneSpectrum (𝓞 L)) (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → χ.inf k * χ.val v ^ h = 1 → χ.valTw ((r : ℝ) / 2) v ∈ kummerField φ₀ h := by
  intro L _ _ _ _ φ₀ I _ φ hφ χ n r hinf hev v h k hk hχ
  choose s hs using exists_aut φ₀
  choose m hm using hev
  have hkm : (k : L) ∈ powIdealElts L h := ⟨k.ne_zero, _, hk⟩
  have hsm : ∀ τ, s τ (k : L) ∈ powIdealElts L h := fun τ => map_mem_pow (s τ : L →+* L) hkm
  have hy : ∏ i, ((s (φ i) k ^ n i)⁻¹ * (s (φ i) k * s ((starRingEnd ℂ).comp (φ i)) k) ^ m i) ∈ powIdealElts L h :=
    prod_mem_pow _ _ fun i _ => mul_mem_pow (inv_mem_pow (zpow_mem_pow (hsm _) _))
      (zpow_mem_pow (mul_mem_pow (hsm _) (hsm _)) _)
  refine mem_kummerField φ₀ hy ?_
  have hp := congrArg (Units.val : ℂˣ → ℂ) hχ
  rw [Units.val_mul, hinf, Units.val_one, Units.val_pow_eq_pow_val] at hp
  have hN := absNorm_pow_eq_prod_sq φ hφ v h k hk
  have hpow : ∀ m : ℕ, (m : ℂ) ^ (-(((r : ℝ) / 2 : ℝ) : ℂ)) = (((m : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast, Complex.ofReal_neg]
  have hreal : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2))) ^ h = (∏ i, ‖φ i k‖) ^ (-r) := by
    have h0 : 0 ≤ ∏ i, ‖φ i k‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [Real.rpow_pow_comm (Nat.cast_nonneg _), hN, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hc : χ.valTw ((r : ℝ) / 2) v ^ h = ((χ.val v : ℂˣ) : ℂ) ^ h * ∏ i, ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) := by
    unfold HChar.valTw
    rw [hpow, mul_pow, ← Complex.ofReal_pow, hreal, Finset.prod_zpow, Complex.ofReal_zpow, Complex.ofReal_prod]
  rw [hc, eq_inv_of_mul_eq_one_right hp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := by simp
  rw [map_mul, map_inv₀, map_zpow₀, map_zpow₀, map_mul, ← hs, ← hs, RingHom.comp_apply, Complex.mul_conj', sq,
    mul_zpow, ← zpow_add₀ hz', ← hm, sub_eq_add_neg, zpow_add₀ hz', div_zpow, inv_div, div_eq_mul_inv]
  ring

end GlobalTheory.Mem.FieldsEx
