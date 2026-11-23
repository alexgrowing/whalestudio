import Mathlib

open ArithmeticFunction

namespace HostParam

structure AbField where
  N : ℕ
  N_pos : 0 < N
  H : Subgroup (ZMod N)ˣ

namespace AbField

variable (E : AbField)

abbrev Gal : Type := (ZMod E.N)ˣ ⧸ E.H

def res : (ZMod E.N)ˣ →* E.Gal := QuotientGroup.mk' E.H

def conj : E.Gal := E.res (-1)

def IsReal : Prop := (-1 : (ZMod E.N)ˣ) ∈ E.H

def inertiaUnits (p : ℕ) : Subgroup (ZMod E.N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd E.N p)).ker

def inertia (p : ℕ) : Subgroup E.Gal := (E.inertiaUnits p).map E.res

def Ramified (p : ℕ) : Prop := E.inertia p ≠ ⊥

def frob (p : ℕ) (hp : p.Coprime E.N) : E.Gal := E.res (ZMod.unitOfCoprime p hp)

def IsModulus (M : ℕ) : Prop := ∃ h : M ∣ E.N, (ZMod.unitsMap h).ker ≤ E.H

noncomputable def conductor : ℕ := sInf {M : ℕ | E.IsModulus M}

def chars : Set (DirichletCharacter ℂ E.N) := {χ | ∀ u ∈ E.H, χ (u : ZMod E.N) = 1}

noncomputable def toGalChar (χ : DirichletCharacter ℂ E.N) (hχ : χ ∈ E.chars) : E.Gal →* ℂˣ :=
  QuotientGroup.lift E.H χ.toUnitHom (fun u hu => by
    rw [MonoidHom.mem_ker]; ext; simpa using hχ u hu)

end AbField

def SplitsIn (d p : ℕ) : Prop :=
  p ≠ d ∧ (p = 2 → d % 8 = 7) ∧ (p ≠ 2 → jacobiSym (-(d : ℤ)) p = 1)

noncomputable def quadCharNeg (d : ℕ) : DirichletCharacter ℂ d :=
  if h : d.Prime then
    letI : Fact d.Prime := ⟨h⟩
    (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  else 1

noncomputable def AbField.chOf (E : AbField) (d : ℕ) (h : d ∣ E.N) : DirichletCharacter ℂ E.N :=
  DirichletCharacter.changeLevel h (quadCharNeg d)

noncomputable def logDerivAtOne {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) : ℂ :=
  deriv (DirichletCharacter.LFunction ψ) 1 / DirichletCharacter.LFunction ψ 1

noncomputable def Gfun {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  (∑ r ∈ Finset.range (⌊y⌋₊ + 1), (Λ r : ℂ) * ψ r * ((y / r - 1 : ℝ) : ℂ)) +
    haveI := Classical.propDecidable (ψ = 1)
    if ψ = 1 then ((-(y * Real.log y) + (1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)
    else (y : ℂ) * logDerivAtOne ψ

end HostParam
