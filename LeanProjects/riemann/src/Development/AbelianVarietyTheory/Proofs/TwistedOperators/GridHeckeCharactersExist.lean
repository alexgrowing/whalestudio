import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.HeckeCharsOfSquare

variable {D : D7}

theorem isHeckeChar_mul {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ * ψ) :=
  ⟨hχ.1.mul hψ.1, fun x => by rw [MonoidHom.mul_apply, hχ.2 x, hψ.2 x, mul_one]⟩

theorem isHeckeChar_inv {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨hχ.1.inv, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

theorem isHeckeChar_div {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ / ψ) := by
  rw [div_eq_mul_inv]; exact isHeckeChar_mul hχ (isHeckeChar_inv hψ)

theorem isHeckeChar_pow {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (n : ℕ) : IsHeckeChar D (χ ^ n) :=
  ⟨hχ.1.pow n, fun x => by rw [MonoidHom.pow_apply, hχ.2 x, one_pow]⟩

theorem resEta_of_mod {χ : (AE D)ˣ →* Circle} {a b : ℕ} (h : ResEta D χ a) (hab : a % 2 = b % 2) : ResEta D χ b := by
  refine ⟨h.1, fun η hη x => ?_⟩
  rw [h.2 η hη x, ← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x, one_pow, one_pow, hab]

theorem resEta_mul {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ * ψ) (a + b) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.mul_apply, hχ.2 η hη x, hψ.2 η hη x, pow_add]⟩

theorem resEta_inv {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) : ResEta D χ⁻¹ a := by
  refine ⟨hχ.1, fun η hη x => ?_⟩
  rw [MonoidHom.inv_apply, hχ.2 η hη x, ← inv_pow]
  have h2 := GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x
  rw [inv_eq_of_mul_eq_one_right (by rw [← sq, h2] : η x * η x = 1)]

theorem resEta_pow {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) (k : ℕ) : ResEta D (χ ^ k) (a * k) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.pow_apply, hχ.2 η hη x, pow_mul]⟩

theorem resEta_div {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ / ψ) (a + b) := by
  rw [div_eq_mul_inv]; exact resEta_mul hχ (resEta_inv hψ)

theorem resEta_of_att {μ η : (AE D)ˣ →* Circle} {a b : ℕ} (ha : ResEta D (Lift.attChr μ η a) a)
    (hb : ResEta D (Lift.attChr μ η b) b) (hab : Odd (a + b)) : ResEta D μ 0 ∧ ResEta D η 1 := by
  rcases Nat.even_or_odd a with hae | hao
  · have hbo : Odd b := (Nat.odd_add'.1 hab).2 hae
    have hna : ¬ Odd a := Nat.not_odd_iff_even.2 hae
    simp only [Lift.attChr, hna, if_false] at ha
    simp only [Lift.attChr, hbo, if_true] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod ha (by rw [Nat.even_iff.1 hae])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := a + b) ?_ (by rw [Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div ha hb
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · exact absurd hab (Nat.not_odd_iff_even.2 (hao.add_odd h))
    have hnb : ¬ Odd b := Nat.not_odd_iff_even.2 hbe
    simp only [Lift.attChr, hao, if_true] at ha
    simp only [Lift.attChr, hnb, if_false] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod hb (by rw [Nat.even_iff.1 hbe])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := b + a) ?_ (by rw [add_comm, Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div hb ha

end GlobalTheory.HeckeCharsOfSquare

namespace GlobalTheory.HeckeCharsOfSquare

end GlobalTheory.HeckeCharsOfSquare
