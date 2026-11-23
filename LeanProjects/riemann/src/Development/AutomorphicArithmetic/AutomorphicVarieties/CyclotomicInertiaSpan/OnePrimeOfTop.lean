import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

namespace UpperTheory.V

instance (A : AbF) : NeZero A.m := ⟨A.pos.ne'⟩

namespace B1

section Cyc

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N]

include F in
theorem natCard_roots : Nat.card (rootsOfUnity N Ω) = N := by
  haveI := IsAlgClosure.isAlgClosed F (K := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  exact hζ.card_rootsOfUnity

def cycN : G F Ω →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Ω (natCard_roots F Ω N)).comp (MulSemiringAction.toRingAut (G F Ω) Ω)

theorem cycN_spec (g : G F Ω) {ζ : Ω} (h : ζ ^ N = 1) : g ζ = ζ ^ (cycN F Ω N g : ZMod N).val := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne N] at h
  have hu : Units.mk0 ζ hz ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [h]
  have key := modularCyclotomicCharacter.spec Ω (natCard_roots F Ω N)
    (MulSemiringAction.toRingAut (G F Ω) Ω g) hu
  simpa [cycN] using key

theorem cycN_eq_iff (g : G F Ω) (b : (ZMod N)ˣ) :
    cycN F Ω N g = b ↔ ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (b : ZMod N).val := by
  constructor
  · rintro rfl ζ hζ
    exact cycN_spec F Ω N g hζ
  · intro hb
    have hz : ∀ t ∈ rootsOfUnity N Ω, (MulSemiringAction.toRingAut (G F Ω) Ω g) (t : Ω) = (t : Ω) ^ (b : ZMod N).val := by
      intro t ht
      have ht' : (t : Ω) ^ N = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      simpa using hb t ht'
    have := modularCyclotomicCharacter.unique Ω (natCard_roots F Ω N)
      (MulSemiringAction.toRingAut (G F Ω) Ω g) hz
    ext
    exact this.symm

end Cyc

def sgL (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (L : Type) [Field L] [NumberField L] [Algebra L K] [Normal ℚ L] : (ZMod M)ˣ →* Gal(L/ℚ) :=
  (AlgEquiv.restrictNormalHom L).comp (Stick.sg M K).toMonoidHom

def leg {N : ℕ} (q : ℕ) [Fact q.Prime] (h : q ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  (quadraticChar (ZMod q)).toUnitHom.comp (ZMod.unitsMap h)

section Coord

variable (n q d : ℕ) [Fact q.Prime] [Fact d.Prime]

abbrev lev (n q d : ℕ) : ℕ := 2 ^ n * q * d

instance : NeZero (lev n q d) :=
  ⟨mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) (Fact.out : q.Prime).ne_zero) (Fact.out : d.Prime).ne_zero⟩

omit [Fact q.Prime] [Fact d.Prime] in
theorem two_dvd_lev : 2 ^ n ∣ lev n q d := (dvd_mul_right _ _).mul_right _
omit [Fact q.Prime] [Fact d.Prime] in
theorem q_dvd_lev : q ∣ lev n q d := (dvd_mul_left _ _).mul_right _
omit [Fact q.Prime] [Fact d.Prime] in
theorem d_dvd_lev : d ∣ lev n q d := dvd_mul_left _ _

abbrev Co (n : ℕ) : Type := (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ

def coord : (ZMod (lev n q d))ˣ →* Co n :=
  (ZMod.unitsMap (two_dvd_lev n q d)).prod ((leg q (q_dvd_lev n q d)).prod (leg d (d_dvd_lev n q d)))

def pmCo (n k : ℕ) (h : k ≤ n) : Subgroup (Co n) :=
  ((Subgroup.zpowers (-1 : (ZMod (2 ^ k))ˣ)).comap (ZMod.unitsMap (pow_dvd_pow 2 h))).prod ⊥

def Es (s q d : ℕ) [Fact q.Prime] [Fact d.Prime] : AbF :=
  ⟨lev (s + 2) q d, NeZero.pos _, (pmCo (s + 2) (s + 2) le_rfl).comap (coord (s + 2) q d)⟩

end Coord

end B1

namespace AbF

open B1

def U (A : AbF) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] : Subgroup (G ℚ Ω) := A.H.comap (cycN ℚ Ω A.m)

def plus (A : AbF) : AbF := ⟨A.m, A.pos, A.H ⊔ Subgroup.zpowers (-1)⟩

def comp (A B : AbF) : AbF :=
  ⟨Nat.lcm A.m B.m, Nat.lcm_pos A.pos B.pos,
    A.H.comap (ZMod.unitsMap (Nat.dvd_lcm_left _ _)) ⊓ B.H.comap (ZMod.unitsMap (Nat.dvd_lcm_right _ _))⟩

def ine (A : AbF) (p : ℕ) : Subgroup (ZMod A.m)ˣ := B3.pPart A.m p

def dec (A : AbF) (p : ℕ) : Subgroup (ZMod A.m)ˣ := levelDec p A.m

def Genus (A : AbF) : Prop :=
  ∀ f : ℕ → (ZMod A.m)ˣ, (∀ p ∈ A.m.primeFactors, f p ∈ A.ine p) → ∏ p ∈ A.m.primeFactors, f p ∈ A.H →
    ∀ p ∈ A.m.primeFactors, f p ∈ A.H

def OnePrime (A : AbF) (p : ℕ) : Prop := A.dec p ⊔ A.H = ⊤

end AbF

end UpperTheory.V

end
