import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem norm_pow_index_le_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup (GQ l)), H.index ≠ 0 → ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖x‖ < 1 → ‖x‖ ^ H.index ≤ ‖((l : ℕ) : Om l)‖ := by
  intro l _ H hidx x hx hx1
  have hfin : Fintype (GQ l ⧸ H) := Subgroup.fintypeOfIndexNeZero hidx
  have fout : ∀ g : GQ l, (g : GQ l ⧸ H).out x = g x := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, AlgEquiv.mul_apply, hx h h.2]
  have hfix : ∀ g : GQ l, g (∏ q : GQ l ⧸ H, q.out x) = ∏ q : GQ l ⧸ H, q.out x := fun g => by
    rw [map_prod, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ H => q.out x]
    refine Finset.prod_congr rfl fun q _ => ?_
    have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ H) := by
      rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [e, fout, AlgEquiv.mul_apply]
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have hn : ‖c‖ = ‖x‖ ^ H.index := by
    rw [← norm_algebraMap' (Om l) c, hc, norm_prod]
    refine (Finset.prod_congr rfl fun q _ => GlobalTheory.RingBasics.norm_gal (Quotient.out q) x).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    rfl
  have hc1 : ‖c‖ < 1 := hn ▸ pow_lt_one₀ (norm_nonneg x) hx1 hidx
  have h2 : ‖c‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hc1
  rw [← hn, ← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  simpa using h2

end GlobalTheory.Per
