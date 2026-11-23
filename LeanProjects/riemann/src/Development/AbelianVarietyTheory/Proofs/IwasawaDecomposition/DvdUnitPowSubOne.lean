import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem unit_pow_congr_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E),
    M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  intro E _ _ u M hM
  set I : Ideal (𝓞 E) := Ideal.span {M} with hI
  have hIb : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hM
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hIb
  haveI : Finite (𝓞 E ⧸ I)ˣ := Finite.of_injective (fun x : (𝓞 E ⧸ I)ˣ => (x : 𝓞 E ⧸ I)) (fun a b h => Units.ext h)
  set v : (𝓞 E ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝓞 E →* 𝓞 E ⧸ I) u with hv
  refine ⟨orderOf v, (isOfFinOrder_of_finite v).orderOf_pos, ?_⟩
  have h1 : v ^ orderOf v = 1 := pow_orderOf_eq_one v
  have h2 : Ideal.Quotient.mk I ((u ^ orderOf v : (𝓞 E)ˣ) : 𝓞 E) = Ideal.Quotient.mk I 1 := by
    have := congrArg (fun w : (𝓞 E ⧸ I)ˣ => (w : 𝓞 E ⧸ I)) h1
    simp only [hv, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at this
    simpa [Units.val_pow_eq_pow_val, map_pow] using this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h2)

end GlobalTheory.UnipKill
