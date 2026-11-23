import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.IsImagQuad
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDefs

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat

noncomputable def fieldUnits (N : ℕ) [NeZero N] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (galEquivZMod N K).toMonoidHom

noncomputable def fieldChars (N : ℕ) [NeZero N] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) :
    Subgroup (DirichletCharacter ℂ N) :=
  annihilator ℂ (fieldUnits N E : Set (ZMod N)ˣ)

open Classical in

noncomputable def rootWeight (l m : ℕ) : ℚ :=
  if m ≠ 1 ∧ ∃ s, m = l ^ s then 1 / (Nat.totient m : ℚ) else 0

end KStar.Ram
