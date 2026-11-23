import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FrobDeriv

def FrobTwist (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (M : Type) : Type := M

variable {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime]
  [CharP K p]

instance : AddCommGroup (FrobTwist K p M) := inferInstanceAs (AddCommGroup M)

noncomputable instance : Module K (FrobTwist K p M) :=
  Module.compHom M (frobenius K p)

theorem twist_smul (c : K) (m : FrobTwist K p M) :
    c • m = (c ^ p • (show M from m) : M) := by
  show (frobenius K p c) • (show M from m) = _
  rw [frobenius_def]

end GlobalTheory.DI.FrobDeriv

open GlobalTheory.DI.FrobDeriv in
theorem GlobalTheory.DI.frobDeriv_factors_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  intro K _ M _ _ p _ _ φ hφ
  let ψ : K →ₗ[ℤ] FrobTwist K p M := (φ : K →+ M).toIntLinearMap
  have hone : φ 1 = 0 := by
    have h := hφ 1 1
    simp only [mul_one, one_pow, one_smul] at h
    have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  let D : Derivation ℤ K (FrobTwist K p M) :=
    { toLinearMap := ψ
      map_one_eq_zero' := hone
      leibniz' := fun a b => by
        show φ (a * b) = a • (show FrobTwist K p M from φ b) + b • (show FrobTwist K p M from φ a)
        rw [twist_smul, twist_smul, hφ]; rfl }
  refine ⟨(D.liftKaehlerDifferential).toAddMonoidHom, ?_, ?_⟩
  · intro c v
    show D.liftKaehlerDifferential (c • v) = _
    rw [LinearMap.map_smul, twist_smul]
    rfl
  · intro a
    show D.liftKaehlerDifferential (KaehlerDifferential.D ℤ K a) = φ a
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
