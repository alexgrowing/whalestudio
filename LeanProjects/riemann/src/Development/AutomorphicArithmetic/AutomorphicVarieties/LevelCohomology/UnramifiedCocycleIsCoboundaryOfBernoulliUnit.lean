import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.V.ML UpperTheory.V.Bern

namespace UpperTheory.V.X

def prodX {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n)) :
    DirichletCharacter R (f * 2 ^ n) :=
  DirichletCharacter.changeLevel (dvd_mul_right f (2 ^ n)) φ * DirichletCharacter.changeLevel (dvd_mul_left (2 ^ n) f) ξ

structure XData (l d : ℕ) {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n)) : Prop where
  d_pos : 0 < d
  four : 4 ∣ l ^ d - 1
  f_odd : Odd f
  prim : φ.IsPrimitive
  ord : orderOf φ ∣ l ^ d - 1
  prim2 : ξ.IsPrimitive
  big : f * 4 ^ (l ^ d - 1).factorization 2 ≤ 2 ^ n
  odd : φ (-1) * ξ (-1) = -1

def LemmaX : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d f n : ℕ) (φ : DirichletCharacter (PadicAlgCl l) f) (ξ : DirichletCharacter (PadicAlgCl l) (2 ^ n)),
    XData l d φ ξ → ‖genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → PadicAlgCl l)‖ = 1

section

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def redChar {O k : Type} [CommRing O] [Field k] (red : O →+* k) {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) : G ℚ Ω →* kˣ :=
  (Units.map red.toMonoidHom).comp (Chr.dirG ℚ Ω χ)

variable {Ω}

def UnrEv (l : ℕ) {k : Type} [Field k] (γ : G ℚ Ω →* kˣ) (c : G ℚ Ω → k) : Prop :=
  ∀ A : ValuationSubring Ω, ∃ H : Subgroup (G ℚ Ω), ¬ l ∣ H.relIndex (Ine (F := ℚ) A ⊓ γ.ker) ∧
    ∀ g ∈ H, g ∈ Ine (F := ℚ) A → γ g = 1 → c g = 0

end

def UnramifiedCocycleIsCoboundaryOfBernoulliUnit : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (c : HV.Coef l) (k : Type) [Field k] [CharP k l]
    (red : c.O →+* k) (N : ℕ) [NeZero N] (χ : DirichletCharacter c.O N), χ ≠ 1 → ¬ l ∣ orderOf χ →
    (∃ g : G ℚ Ω, (redChar Ω red χ g : k) ≠ red (chiO ℚ Ω l c.O g : c.O)) →
    ‖genB 1 (χ⁻¹.ringHomComp c.O.val.toRingHom : ZMod N → PadicAlgCl l)‖ = 1 →
    ∀ z : G ℚ Ω → k, IsCoc (redChar Ω red χ) z → UnrEv l (redChar Ω red χ) z → ∃ m : k, ∀ g, z g = (redChar Ω red χ g : k) * m - m

def CorX : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (k : Type) [Field k] [CharP k l]
    (red : c.O →+* k) (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ →
    ∀ γ : G ℚ Ω →* kˣ, (γ = redChar Ω red (prodX φ ξ) ∨ γ = (redChar Ω red (prodX φ ξ))⁻¹) →
    ∀ z : G ℚ Ω → k, IsCoc γ z → UnrEv l γ z → ∃ m : k, ∀ g, z g = (γ g : k) * m - m

end UpperTheory.V.X

end
