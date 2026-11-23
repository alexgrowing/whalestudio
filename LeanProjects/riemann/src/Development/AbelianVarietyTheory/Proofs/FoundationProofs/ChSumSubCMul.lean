import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KZ.Cmp

variable {l : ℕ} [Fact l.Prime]

def chSum (F : PowerSeries (Qbar l)) (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val)

def gSum (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * z ^ (b : ZMod (l ^ m)).val

def rSum (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) : Qbar l :=
  ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass F r ξ x

def InComp (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Prop :=
  ∀ b : (ZMod (l ^ m))ˣ, b ^ (l - 1) = 1 →
    ‖ψ⁻¹ (b : ZMod (l ^ m)) - (((b : ZMod (l ^ m)).val : Qbar l) ^ e) * φ (((b : ZMod (l ^ m)).val : ℕ) : ZMod l)‖ < 1

theorem tval_sub_C_mul (F G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (F - PowerSeries.C a * G) N z = tval F N z - a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sub, PowerSeries.coeff_C_mul]; ring

theorem tval_C_mul (G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (PowerSeries.C a * G) N z = a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_C_mul]; ring

end GlobalTheory.KZ.Cmp
