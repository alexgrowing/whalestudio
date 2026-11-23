import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

noncomputable section

open Finset

namespace UpperTheory.V.Stk

open UpperTheory.V.Bern

def Ev (M k : ℕ) (b : ZMod M) : ℚ := bcoef M k b.val / k

def yCl {M : ℕ} (a : ℕ) (b : ZMod M) : ZMod M := (a : ZMod M)⁻¹ * b

def Eva (M k a : ℕ) (b : ZMod M) : ℚ := Ev M k b - (a : ℚ) ^ k * Ev M k (yCl a b)

def jv (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) * (yCl a b).val - b.val) / M

def Eone (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) - 1) / 2 - jv M a b

def dk (k : ℕ) : ℕ := 2 * k * primorial (k + 1)

def ck (l k : ℕ) : ℕ := padicValNat l (dk k)

theorem dk_pos {k : ℕ} (hk : 0 < k) : 0 < dk k := by
  unfold dk
  exact Nat.mul_pos (by omega) (primorial_pos _)

def SamePrimes (N M : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N

section Elements

variable {M : ℕ} [NeZero M] {Γ : Type} [Group Γ]

def sumEl {R : Type} [CommRing R] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → R) : MonoidAlgebra R Γ :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (φ b)⁻¹ (f b)

def yForm (k a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := -sumEl φ (Eva M k a)

def xEl (a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ (Eone M a)

def ytEl (e a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ fun b => (b.val : ℤ) ^ e * Eone M a b

end Elements

section Maps

variable {G Γ : Type} [Group G] [Group Γ]

abbrev cf (R Γ : Type) [CommRing R] [Group Γ] : MonoidAlgebra ℤ Γ →+* MonoidAlgebra R Γ :=
  MonoidAlgebra.mapRingHom Γ (Int.castRingHom R)

theorem cf_single (R : Type) [CommRing R] (g : Γ) (n : ℤ) :
    cf R Γ (MonoidAlgebra.single g n) = MonoidAlgebra.single g (n : R) := by
  simp [cf]

theorem cf_sumEl (R : Type) [CommRing R] {M : ℕ} [NeZero M] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → ℤ) :
    cf R Γ (sumEl φ f) = sumEl φ fun b => (f b : R) := by
  simp only [sumEl, map_sum, cf_single]

theorem sumEl_add {R : Type} [CommRing R] {M : ℕ} [NeZero M] (φ : (ZMod M)ˣ →* Γ) (f g : ZMod M → R) :
    sumEl φ (fun b => f b + g b) = sumEl φ f + sumEl φ g := by
  simp only [sumEl, MonoidAlgebra.single_add, Finset.sum_add_distrib]

def twHom {R : Type} [CommRing R] (κ : G →* Rˣ) (π : G →* Γ) (e : ℕ) : G →* MonoidAlgebra R Γ where
  toFun g := MonoidAlgebra.single (π g) (((κ g)⁻¹ ^ e : Rˣ) : R)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single, mul_pow, mul_comm]

def tw {R : Type} [CommRing R] (κ : G →* Rˣ) (π : G →* Γ) (e : ℕ) : MonoidAlgebra ℤ G →+* MonoidAlgebra R Γ :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra R Γ) G (twHom κ π e)).toRingHom

end Maps

example : Eone 7 5 1 = 0 := by
  have h : ((5 : ℕ) : ZMod 7)⁻¹ = 3 := ZMod.inv_eq_of_mul_eq_one 7 _ _ (by decide)
  rw [Eone, jv, yCl, h]
  decide

end UpperTheory.V.Stk

end
