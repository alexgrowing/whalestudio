import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycleStatement
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB.TwistCochain

theorem pow_mod_of_pow_eq_one' {Ω : Type} [Field Ω] {N : ℕ} {ζ : Ω} (hN : ζ ^ N = 1) (n : ℕ) :
    ζ ^ (n % N) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n N, pow_add, pow_mul, hN, one_pow, one_mul]

theorem twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  intro K Ω _ _ _ _ N ζ hN hζ hζfix a b α β ha hb hα hβ w hw hcoc
  haveI : NeZero N := ⟨hN.ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha ((algebraMap K Ω).injective (by rw [← hα, map_zero]))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((algebraMap K Ω).injective (by rw [← hβ, map_zero]))
  obtain ⟨-, hgα, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hζfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hylc, -, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hζfix hβ0 ⟨b, hβ.symm⟩
  refine ⟨fun g => Units.mk0 α hα0 ^ (kum (N := N) ζ β g).val * (w g)⁻¹, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hylc hw (fun (i : ZMod N) (u : Ωˣ) => Units.mk0 α hα0 ^ i.val * u⁻¹)
  · intro g h
    have hwg : (w g : Ω) ≠ 0 := (w g).ne_zero
    have hwh : g (w h : Ω) ≠ 0 := by simpa using (w h).ne_zero
    have hwgh : (w (g * h) : Ω) ≠ 0 := (w (g * h)).ne_zero
    have hz : ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val =
        (ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val := by
      rw [ZMod.val_mul, pow_mod_of_pow_eq_one' hζ.pow_eq_one, pow_mul]
    have hc := hcoc g h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hgα g, hz]
    rw [pow_add] at hc
    field_simp
    rw [mul_pow]
    linear_combination -(ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val * hc

end GlobalTheory.NeedB.TwistCochain
