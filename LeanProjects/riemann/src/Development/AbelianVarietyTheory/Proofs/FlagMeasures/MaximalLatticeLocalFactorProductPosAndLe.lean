import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.MaxLatLam

theorem factor_bounds {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    0 < (q ^ n - (-1) ^ n) / (q + 1) ∧ (q ^ n - (-1) ^ n) / (q + 1) ≤ (q ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : q ≤ q ^ n := le_self_pow₀ (by linarith) (by omega)
  have h2 : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := neg_one_pow_eq_or ℝ n
  have h3 : (q ^ 2) ^ ((n : ℝ) / 2) = q ^ n := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast q n]
    congr 1
    push_cast
    ring
  refine ⟨div_pos (by rcases h2 with e | e <;> rw [e] <;> linarith) (by linarith), ?_⟩
  rw [h3, div_le_iff₀ (by linarith)]
  rcases h2 with e | e <;> rw [e] <;> nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → 1 ≤ Module.finrank K V → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → 0 < lamMax h M ∧ lamMax h M ≤ (discN h M : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd hn M hM
  obtain ⟨hfin, hd, -, hP⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM
  rw [hd, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin]
  have hq : ∀ P ∈ hfin.toFinset, (2 : ℝ) ≤ (qIn P : ℝ) := fun P hp => by
    exact_mod_cast (hP P (hfin.mem_toFinset.1 hp)).2.1
  refine ⟨Finset.prod_pos fun P hp => (factor_bounds (hq P hp) hn).1, ?_⟩
  rw [Nat.cast_prod, ← Real.finset_prod_rpow _ _ (fun P _ => Nat.cast_nonneg _)]
  refine Finset.prod_le_prod (fun P hp => (factor_bounds (hq P hp) hn).1.le) fun P hp => ?_
  rw [(hP P (hfin.mem_toFinset.1 hp)).2.2.1, Nat.cast_pow]
  exact (factor_bounds (hq P hp) hn).2

end GlobalTheory.MaxLatLam
