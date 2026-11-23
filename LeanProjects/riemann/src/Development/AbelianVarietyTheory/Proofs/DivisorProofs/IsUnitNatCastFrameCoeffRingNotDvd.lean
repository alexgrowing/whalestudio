import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.ExpFrame.Frame

theorem isUnit_natCast_of_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok →
    ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  intro l _ ι _ N F hF n hn
  obtain ⟨hinj, L, _, hrange⟩ := hF.ring
  have hnorm : ‖(n : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) n, PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hn
  have hne : (n : PadicAlgCl l) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hmem : (n : PadicAlgCl l)⁻¹ ∈ Set.range F.emb := by
    rw [hrange]
    refine ⟨?_, ?_⟩
    · exact L.inv_mem (L.natCast_mem n)
    · rw [norm_inv, hnorm, inv_one]
  obtain ⟨y, hy⟩ := hmem
  have h1 : (n : F.O) * y = 1 := by
    apply hinj
    rw [map_mul, map_natCast, hy, map_one, mul_inv_cancel₀ hne]
  exact IsUnit.of_mul_eq_one y h1

end GlobalTheory.ExpFrame.Frame
