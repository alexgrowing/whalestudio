import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParPinsOfRec
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem exp_div_mul_eq_zpow_mul_zpow {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Nat.Coprime p q) :
    ∃ a b : ℤ, Complex.exp (2 * Real.pi * Complex.I / ((p * q : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / ((p * (p - 1) : ℕ) : ℂ)) ^ a *
        Complex.exp (2 * Real.pi * Complex.I / ((q * (q - 1) : ℕ) : ℂ)) ^ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨v * p', u * q', ?_⟩
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have h1 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (q' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h3 : (p' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h4 : (q' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h5 : (u : ℂ) * (p' + 1) + v * (q' + 1) = 1 := by exact_mod_cast huv
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * h5

theorem Base.exists_root_mul (B : Base) : ∃ y : B.O, B.embLL (B.OtoLL y) =
    Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
  have p0 := B.host.g_prime 0
  have p1 := B.host.g_prime 1
  obtain ⟨z₀, hz₀, e₀⟩ := B.roots_Ks (B.host.g 0 * (B.host.g 0 - 1)) (by simp)
  obtain ⟨z₁, hz₁, e₁⟩ := B.roots_Ks (B.host.g 1 * (B.host.g 1 - 1)) (by simp)
  obtain ⟨a, b, hab⟩ := exp_div_mul_eq_zpow_mul_zpow p0.two_le p1.two_le
    ((Nat.coprime_primes p0 p1).2 B.host.g_ne)
  have hmem : z₀ ^ a * z₁ ^ b ∈ B.Ks := mul_mem (zpow_mem hz₀ a) (zpow_mem hz₁ b)
  have he : B.embLL (z₀ ^ a * z₁ ^ b) =
      Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
    rw [map_mul, map_zpow₀, map_zpow₀, e₀, e₁, hab]
  have hne : B.host.g 0 * B.host.g 1 ≠ 0 := mul_ne_zero p0.ne_zero p1.ne_zero
  have hint : IsIntegral ℤ (B.embLL (z₀ ^ a * z₁ ^ b)) := by
    rw [he]
    exact (Complex.isPrimitiveRoot_exp _ hne).isIntegral (Nat.pos_of_ne_zero hne)
  have hint' : IsIntegral ℤ (z₀ ^ a * z₁ ^ b) :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hint
  refine ⟨⟨⟨z₀ ^ a * z₁ ^ b, hmem⟩, ?_⟩, he⟩
  exact (isIntegral_algHom_iff (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom Subtype.val_injective).1 hint'

theorem hermitianCodeWordStages_has_rootOfUnity : ∀ X : Stages, OZeta X.toD7 := fun X => X.B.exists_root_mul

end GlobalTheory.Mem
