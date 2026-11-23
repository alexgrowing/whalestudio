import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
open NumberField
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCS

theorem norm_sum_sq_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (X lam : Fin N → ℂ) :
    ‖∑ j, X j * lam j‖ ^ 2 ≤ (∑ i, ‖(A⁻¹.mulVec X) i‖ ^ 2) * ∑ a, ‖∑ m, A m a * lam m‖ ^ 2 := by
  set Y := A⁻¹.mulVec X with hY
  have hX : X = A.mulVec Y := by
    rw [hY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
  have e : ∑ j, X j * lam j = ∑ a, Y a * ∑ m, A m a * lam m := by
    rw [hX]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  calc ‖∑ a, Y a * ∑ m, A m a * lam m‖ ^ 2 ≤ (∑ a, ‖Y a‖ * ‖∑ m, A m a * lam m‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
        simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end GlobalTheory.FrameCS

open GlobalTheory.FrameCS in

theorem GlobalTheory.frame_semilinear_sq_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (σ : K →+* ℂ) (ℓ : W → ℂ), GlobalTheory.CompHt.IsFrame Nm W b g A → (∀ k, (gw k : V) = ∑ j, g j k • b j) → (∀ j, b j = ∑ k, c k j • (gw k : V)) → (∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) → ∀ x : W, ‖ℓ x‖ ^ 2 ≤ Nm σ x ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 := by
  intro K V _ _ _ _ _ _ Nm W N n b g A c gw σ ℓ hF hg hc hℓ x
  set lam : Fin N → ℂ := fun j => ∑ k, σ (c k j) * ℓ (gw k) with hlam

  have h2 : ∀ k, ℓ (gw k) = ∑ j, σ (g j k) * lam j := by
    intro k
    set e : Fin n → K := fun l => ∑ j, g j k * c l j with he
    have hexp : (gw k : V) = ∑ l, e l • (gw l : V) := by
      rw [hg k]
      simp_rw [hc, he, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
      (Finset.univ.image e)
    choose β hβ using fun l => hd _ (Finset.mem_image_of_mem e (Finset.mem_univ l))
    have hβ' : ∀ l, ((β l : 𝓞 K) : K) = ((d : 𝓞 K) : K) * e l := fun l => by
      rw [← Algebra.smul_def, ← hβ l]
    have hx1 : (((d : 𝓞 K) • gw k : W) : V) = ∑ l, β l • (gw l : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul K, hexp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← algebraMap_smul K (β l), smul_smul]
      congr 1
      exact (hβ' l).symm
    have hx2 : (((d : 𝓞 K) • gw k : W) : V) = ∑ _i : Fin 1, (d : 𝓞 K) • (gw k : V) := by
      simp
    have e1 := hℓ n β gw _ hx1
    have e2 := hℓ 1 (fun _ => (d : 𝓞 K)) (fun _ => gw k) _ hx2
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    have hd0 : σ ((d : 𝓞 K) : K) ≠ 0 := by
      rw [map_ne_zero, ne_eq, RingOfIntegers.coe_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero d
    apply mul_left_cancel₀ hd0
    rw [← e2, e1]
    simp only [hβ', map_mul, hlam, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [he, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hxmem : (x : V) ∈ Submodule.span (𝓞 K) (Set.range fun k => (gw k : V)) := by
    have := hF.span
    have hfun : (fun k => ∑ j, g j k • b j) = fun k => (gw k : V) := funext fun k => (hg k).symm
    rw [hfun] at this
    rw [this]; exact x.2
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hxmem
  have h3 : ℓ x = ∑ j, σ (b.repr x j) * lam j := by
    rw [hℓ n β gw x hβ.symm]
    have hr : ∀ j, b.repr x j = ∑ k, (β k : K) * g j k := by
      intro j
      have hk : ∀ k, β k • (gw k : V) = ∑ j, ((β k : K) * g j k) • b j := by
        intro k
        rw [← algebraMap_smul K, hg k, Finset.smul_sum]
        simp_rw [smul_smul]
      rw [← hβ, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      rw [Module.Basis.repr_sum_self]
    simp only [hr, h2, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hN : Nm σ x ^ 2 = ∑ i, ‖((A σ)⁻¹.mulVec fun j => σ (b.repr x j)) i‖ ^ 2 := by
    rw [← hF.norm σ x, GlobalTheory.ChowHt.frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  have hu : ∀ a, ∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k) = ∑ m, A σ m a * lam m := by
    intro a
    simp only [hlam, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [hu, hN, h3]
  exact norm_sum_sq_le (A σ) (hF.herm σ) _ lam
