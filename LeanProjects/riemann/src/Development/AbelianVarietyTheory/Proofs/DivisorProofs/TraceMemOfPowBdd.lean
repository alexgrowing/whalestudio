import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceBdd

theorem trace_mem_valuationSubring_of_pow_bounded {K : Type} [Field K] (O : ValuationSubring K) [IsNoetherianRing O]
    (n : ℕ) (y : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ O) : y.trace ∈ O := by
  classical

  let N : Submodule O (Matrix (Fin n) (Fin n) K) :=
    Submodule.span O (Set.range fun p : Fin n × Fin n => a⁻¹ • Matrix.single p.1 p.2 (1 : K))
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  haveI : IsNoetherian O N := isNoetherian_of_fg_of_noetherian N hNfg
  have hpow : ∀ k : ℕ, y ^ k ∈ N := by
    intro k
    rw [Matrix.matrix_eq_sum_single (y ^ k)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hc : a * (y ^ k) i j ∈ O := h k i j
    have : Matrix.single i j ((y ^ k) i j) =
        (⟨a * (y ^ k) i j, hc⟩ : O) • (a⁻¹ • Matrix.single i j (1 : K)) := by
      rw [← algebraMap_smul K (⟨a * (y ^ k) i j, hc⟩ : O), smul_smul, Matrix.smul_single, smul_eq_mul]
      congr 1
      change (y ^ k) i j = a * (y ^ k) i j * a⁻¹ * 1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {y}) ≤ N := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    rintro x hx
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hx
    exact hpow k
  have hint : IsIntegral O y :=
    isIntegral_of_submodule_noetherian _ (isNoetherian_of_le hle) y (Algebra.self_mem_adjoin_singleton O y)
  obtain ⟨p, hpm, hp⟩ := hint

  have hpL : aeval (y.map (algebraMap K (AlgebraicClosure K))) (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
    have h1 : aeval y (p.map (algebraMap O K)) = 0 := by
      rw [aeval_map_algebraMap]; exact hp
    have h2 : aeval (y.map (algebraMap K (AlgebraicClosure K)))
          ((p.map (algebraMap O K)).map (algebraMap K (AlgebraicClosure K))) =
        (Algebra.ofId K (AlgebraicClosure K)).mapMatrix (aeval y (p.map (algebraMap O K))) := by
      rw [aeval_map_algebraMap]
      rw [← aeval_algHom_apply]
      rfl
    rw [IsScalarTower.algebraMap_eq O K (AlgebraicClosure K), ← Polynomial.map_map, h2, h1, map_zero]
  have hroot : ∀ μ ∈ (y.map (algebraMap K (AlgebraicClosure K))).charpoly.roots, IsIntegral O μ := by
    intro μ hμ
    have hs : μ ∈ spectrum (AlgebraicClosure K) (y.map (algebraMap K (AlgebraicClosure K))) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
    have hs2 := spectrum.subset_polynomial_aeval (y.map (algebraMap K (AlgebraicClosure K)))
      (p.map (algebraMap O (AlgebraicClosure K))) ⟨μ, hs, rfl⟩
    rw [hpL] at hs2
    have h0 : eval μ (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
      by_contra hc
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Ne.isUnit hc).map _)
    exact ⟨p, hpm, by rwa [eval_map] at h0⟩
  have htr : algebraMap K (AlgebraicClosure K) y.trace = (y.map (algebraMap K (AlgebraicClosure K))).trace := by
    simp [Matrix.trace, map_sum]
  have hL : IsIntegral O (algebraMap K (AlgebraicClosure K) y.trace) := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
    exact multiset_sum_mem _ (fun μ hμ => (mem_integralClosure_iff _ _).2 (hroot μ hμ))
  have hK : IsIntegral O y.trace :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).1 hL
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hK
  rw [← hz]
  exact z.2

end GlobalTheory.TraceBdd

theorem GlobalTheory.trace_mem_of_pow_bdd : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (a : w.adicCompletion E), a ≠ 0 →
    (∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ Ov E w) → y.trace ∈ Ov E w := by
  intro E _ _ w n y a ha h
  exact GlobalTheory.TraceBdd.trace_mem_valuationSubring_of_pow_bounded (w.adicCompletionIntegers E) n y a ha h
