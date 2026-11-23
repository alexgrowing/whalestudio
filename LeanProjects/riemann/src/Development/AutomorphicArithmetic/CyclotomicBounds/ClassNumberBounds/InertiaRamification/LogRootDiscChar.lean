import Mathlib

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

noncomputable def condExp (l : ℕ) (ψ : DirichletCharacter ℂ N) : ℕ :=
  ψ.conductor.factorization l

noncomputable def avgCondExp (l : ℕ) (X : Subgroup (DirichletCharacter ℂ N)) : ℚ :=
  (∑ᶠ ψ : X, (condExp l (ψ : DirichletCharacter ℂ N) : ℚ)) / (Nat.card X : ℚ)

noncomputable def charKer (X : Subgroup (DirichletCharacter ℂ N)) : Subgroup (ZMod N)ˣ :=
  ⨅ ψ ∈ X, (MulChar.toUnitHom ψ).ker

noncomputable def evenPart (X : Subgroup (DirichletCharacter ℂ N)) : Subgroup (DirichletCharacter ℂ N) :=
  X ⊓ annihilator ℂ ({-1} : Set (ZMod N)ˣ)

noncomputable def fieldCond [NeZero N] (X : Subgroup (DirichletCharacter ℂ N)) : ℕ :=
  (Set.toFinite (X : Set (DirichletCharacter ℂ N))).toFinset.lcm fun ψ => ψ.conductor

noncomputable def logRootDiscChar (X : Subgroup (DirichletCharacter ℂ N)) : ℝ :=
  (∑ᶠ ψ : X, Real.log (ψ : DirichletCharacter ℂ N).conductor) / (Nat.card X : ℝ)

def inertiaUnits (N l : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N l)).ker

def decompUnits (N l : ℕ) [NeZero N] [hl : Fact l.Prime] : Subgroup (ZMod N)ˣ :=
  (Subgroup.zpowers (ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl.out (NeZero.ne N)))).comap
    (ZMod.unitsMap (Nat.ordCompl_dvd N l))

def higherUnits (N l t : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.gcd_dvd_left N (ordCompl[l] N * l ^ t))).ker

noncomputable def crtEquiv (N l : ℕ) [NeZero N] [hl : Fact l.Prime] :
    ZMod N ≃+* ZMod (ordProj[l] N) × ZMod (ordCompl[l] N) :=
  (ZMod.ringEquivCongr (Nat.ordProj_mul_ordCompl_eq_self N l).symm).trans
    (ZMod.chineseRemainder
      (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))))

noncomputable def localUnits (N l : ℕ) [NeZero N] [Fact l.Prime] :
    (ZMod (ordProj[l] N))ˣ →* (ZMod N)ˣ :=
  Units.map ((crtEquiv N l).symm.toRingHom.toMonoidHom.comp (MonoidHom.inl _ _))

noncomputable def localPart (N l : ℕ) [NeZero N] [Fact l.Prime] :
    DirichletCharacter ℂ N →* DirichletCharacter ℂ (ordProj[l] N) where
  toFun ψ := MulChar.ofUnitHom ((MulChar.toUnitHom ψ).comp (localUnits N l))
  map_one' := by ext u; simp
  map_mul' ψ χ := by ext u; simp

noncomputable def ramIdx [NeZero N] (l : ℕ) [Fact l.Prime]
    (X : Subgroup (DirichletCharacter ℂ N)) : ℕ :=
  Nat.card (X.map (localPart N l))

noncomputable def ramIdxUnits (l : ℕ) (H : Subgroup (ZMod N)ˣ) : ℕ :=
  Nat.card ((inertiaUnits N l).map (QuotientGroup.mk' H))

noncomputable def vd [NeZero N] (l : ℕ) [Fact l.Prime]
    (X : Subgroup (DirichletCharacter ℂ N)) : ℚ :=
  avgCondExp l (X.map (localPart N l))

def SplitsFor (l : ℕ) (ψ : DirichletCharacter ℂ N) : Prop :=
  ψ.primitiveCharacter (l : ZMod ψ.conductor) = 1

def ConjIn (X : Subgroup (DirichletCharacter ℂ N)) (D : Subgroup (ZMod N)ˣ) : Prop :=
  (-1 : (ZMod N)ˣ) ∈ D ⊔ charKer X

def vdFormula (l a e : ℕ) : ℚ :=
  (a : ℚ) - 1 / ((l : ℚ) - 1) + 1 / (((l : ℚ) - 1) * (l : ℚ) ^ (a - 1)) - 1 / (e : ℚ)

example : vdFormula 3 2 3 = 4 / 3 := by norm_num [vdFormula]
example : vdFormula 7 2 21 = 38 / 21 := by norm_num [vdFormula]

end KStar.Ram
