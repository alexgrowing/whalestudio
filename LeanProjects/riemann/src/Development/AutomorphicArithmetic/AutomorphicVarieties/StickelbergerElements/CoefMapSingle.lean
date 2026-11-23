import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

noncomputable section

open Finset

namespace UpperTheory.V.B4

open UpperTheory.V.Bern

def Ek (M k : ℕ) (b : ZMod M) : ℚ := bcoef M k b.val / k

def yCl {M : ℕ} (a : ℕ) (b : ZMod M) : ZMod M := (a : ZMod M)⁻¹ * b

def Eka (M k a : ℕ) (b : ZMod M) : ℚ := Ek M k b - (a : ℚ) ^ k * Ek M k (yCl a b)

def jv (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) * (yCl a b).val - b.val) / M

def Eone (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) - 1) / 2 - jv M a b

def ck (l k : ℕ) : ℕ := padicValNat l (2 * k * primorial (k + 1))

def Zl (l : ℕ) [Fact l.Prime] : Subring ℚ where
  carrier := {x | ¬ l ∣ x.den}
  zero_mem' := by simpa using (Fact.out : l.Prime).ne_one
  one_mem' := by simpa using (Fact.out : l.Prime).ne_one
  add_mem' {x y} hx hy h := ((Fact.out : l.Prime).dvd_mul.1 (h.trans (Rat.add_den_dvd x y))).elim hx hy
  mul_mem' {x y} hx hy h := ((Fact.out : l.Prime).dvd_mul.1 (h.trans (Rat.mul_den_dvd x y))).elim hx hy
  neg_mem' {x} hx := by simpa using hx

theorem mem_Zl {l : ℕ} [Fact l.Prime] {x : ℚ} : x ∈ Zl l ↔ ¬ l ∣ x.den := Iff.rfl

section Elements

variable {M : ℕ} [NeZero M] {Γ : Type} [CommGroup Γ]

def sumEl {R : Type} [CommRing R] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → R) : MonoidAlgebra R Γ :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (φ b)⁻¹ (f b)

def thetaEl (k : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := -sumEl φ (Ek M k)

def yEl (k a : ℕ) (ha : a.Coprime M) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ :=
  (1 - MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℚ) ^ k)) * thetaEl k φ

def xEl (a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ (Eone M a)

def ytEl (e a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ fun b => (b.val : ℤ) ^ e * Eone M a b

def stickEl (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := sumEl φ fun b => (b.val : ℚ) / M

def normEl (R : Type) [CommRing R] (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra R Γ := sumEl φ fun _ => 1

end Elements

section Maps

variable {G Γ : Type} [CommGroup G] [CommGroup Γ]

def coefMap (R Γ : Type) [CommRing R] [CommGroup Γ] : MonoidAlgebra ℤ Γ →+* MonoidAlgebra R Γ :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra R Γ) Γ (MonoidAlgebra.of R Γ)).toRingHom

theorem coefMap_single (R : Type) [CommRing R] (g : Γ) (n : ℤ) :
    coefMap R Γ (MonoidAlgebra.single g n) = MonoidAlgebra.single g (n : R) := by
  simp [coefMap, MonoidAlgebra.smul_single]

def twHom {R : Type} [CommRing R] (κ : G →* Rˣ) (π : G →* Γ) (e : ℕ) : G →* MonoidAlgebra R Γ where
  toFun g := MonoidAlgebra.single (π g) (((κ g)⁻¹ ^ e : Rˣ) : R)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single, mul_pow, mul_comm]

def tw {R : Type} [CommRing R] (κ : G →* Rˣ) (π : G →* Γ) (e : ℕ) : MonoidAlgebra ℤ G →+* MonoidAlgebra R Γ :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra R Γ) G (twHom κ π e)).toRingHom

def IntAt (l : ℕ) [Fact l.Prime] (r : ℕ) (z : MonoidAlgebra ℚ Γ) : Prop := ∀ g, z.coeff g / (l : ℚ) ^ r ∈ Zl l

end Maps

example : Eone 7 5 1 = 0 := by
  have h : ((5 : ℕ) : ZMod 7)⁻¹ = 3 := ZMod.inv_eq_of_mul_eq_one 7 _ _ (by decide)
  rw [Eone, jv, yCl, h]
  decide

end UpperTheory.V.B4

end
