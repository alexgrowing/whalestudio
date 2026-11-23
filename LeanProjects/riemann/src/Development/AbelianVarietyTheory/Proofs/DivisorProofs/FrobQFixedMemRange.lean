import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtD
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime]

noncomputable def frobQEquiv (r : ℕ) (hr : 0 < r) : Qr p r ≃ₐ[ℚ_[p]] Qr p r :=
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  AlgEquiv.ofBijective (frobQ p r)
    ((frobQ p r).toLinearMap.injective_iff_surjective.mp (frobQ p r).toRingHom.injective |>
      fun hs => ⟨(frobQ p r).toRingHom.injective, hs⟩)

theorem frobQEquiv_pow_apply (r : ℕ) (hr : 0 < r) (i : ℕ) (b : Qr p r) :
    (((frobQEquiv p r hr ^ i) b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  induction i generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
    rfl

theorem orderOf_frobQEquiv (r : ℕ) (hr : 0 < r) : orderOf (frobQEquiv p r hr) = r := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  have key : ∀ i : ℕ, frobQEquiv p r hr ^ i = 1 ↔ r ∣ i := by
    intro i
    rw [← IsFrobOn.pow_fixes_iff p (Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) i]
    constructor
    · intro h x hx
      have := frobQEquiv_pow_apply p r hr i ⟨x, hx⟩
      rw [h] at this
      exact this.symm
    · intro h
      refine AlgEquiv.ext fun b => Subtype.ext ?_
      rw [frobQEquiv_pow_apply]
      exact h _ b.2
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((key r).2 dvd_rfl)
  · exact (key _).1 (pow_orderOf_eq_one _)

end GlobalTheory.LKRes
