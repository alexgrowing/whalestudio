import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem frobenius_affine_integral (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S]
    [ValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] (d : ℕ)
    (U : Matrix (Fin d) (Fin d) S) (z : Fin d → S) (y : Fin d → K)
    (h : ∀ i, y i ^ p = (U.map (algebraMap S K) *ᵥ y) i + algebraMap S K (z i)) :
    ∀ i, y i ∈ (algebraMap S K).range := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set w := ValuationRing.valuation S K with hw
  have hint : ∀ s : S, w (algebraMap S K s) ≤ 1 := fun s =>
    (ValuationRing.mem_integer_iff S K _).2 ⟨s, rfl⟩
  intro i0
  have hi0 : Finset.univ.Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => w (y j)) hi0
  have hM : w (y i) ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hle : w (y i) ^ p ≤ w (y i) := by
      rw [← map_pow, h i]
      refine (Valuation.map_add_le w ?_ ?_)
      · simp only [Matrix.mulVec, dotProduct]
        refine Valuation.map_sum_le w fun j _ => ?_
        rw [map_mul, Matrix.map_apply]
        calc w (algebraMap S K (U i j)) * w (y j) ≤ 1 * w (y i) :=
              mul_le_mul' (hint _) (hmax j (Finset.mem_univ _))
          _ = w (y i) := one_mul _
      · exact (hint _).trans hgt.le
    have h2 : w (y i) ^ 2 ≤ w (y i) ^ p := pow_le_pow_right₀ hgt.le hp
    have h3 : w (y i) * w (y i) ≤ 1 * w (y i) := by
      rw [one_mul, ← sq]; exact h2.trans hle
    have h0 : 0 < w (y i) := lt_trans zero_lt_one hgt
    exact absurd (le_of_mul_le_mul_right h3 h0) (not_le.2 hgt)
  have : w (y i0) ≤ 1 := (hmax i0 (Finset.mem_univ _)).trans hM
  obtain ⟨s, hs⟩ := (ValuationRing.mem_integer_iff S K _).1 this
  exact ⟨s, hs⟩

end GlobalTheory
