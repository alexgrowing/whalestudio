import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
open MvPolynomial

namespace GlobalTheory.WeylIntExpansion

theorem weyl_int_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  intro N Y hY hrep f hf
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  set N0 := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) with hN0
  have hN0ne : N0 ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti _ _ hab
  have hfQ : Formalism.GradedWeylDivisibility.intQ N N f ∈ Formalism.GradedWeylDivisibility.bDual N N le_rfl μ ((Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ).map (Formalism.GradedWeylDivisibility.intQ N N)) := by
    rw [← GlobalTheory.StdDual.weylEqDualNabla N N le_rfl μ hanti]
    exact ⟨f, hf, rfl⟩
  have hmem : ∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ := by
    intro J
    rw [hμ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY]
    exact Submodule.subset_span ⟨J, rfl⟩
  have hz : ∀ J, ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) = z * N0 :=
    fun J => hfQ.2 _ ⟨_, hmem J, rfl⟩
  choose z hz using hz
  refine ⟨z, hz, ?_⟩
  have hmap : ∀ J, map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) =
      GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J => by
    unfold GlobalTheory.WeylMinorDual.colProd
    exact Formalism.L2.DIV.fk_map_bidet _ _ _ _
  have h := hrep (map (Int.castRingHom ℚ) f) hfQ.1
  have hc : ∀ J, Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) (map (Int.castRingHom ℚ) f) = z J * N0 :=
    fun J => by rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← hmap, hz]
  simp only [hc] at h
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply smul_right_injective _ hN0ne
  simp only
  rw [← h, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [map_zsmul, hmap, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm]

end GlobalTheory.WeylIntExpansion
