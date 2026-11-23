import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℤ_[l]ˣ,
    ∀ (g : _root_.Formalism.BasicNotions.Loc.GQ l) (m : ℕ) (x : _root_.Formalism.BasicNotions.Loc.Om l), x ^ (l ^ m) = 1 →
      g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val := by
  intro l _
  haveI : ∀ i, HasEnoughRootsOfUnity (_root_.Formalism.BasicNotions.Loc.Om l) (l ^ i) := fun i => by
    unfold _root_.Formalism.BasicNotions.Loc.Om
    infer_instance
  let ρ : _root_.Formalism.BasicNotions.Loc.GQ l →* (_root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) :=
    { toFun := fun g => (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l), map_one' := rfl, map_mul' := fun _ _ => rfl }
  exact ⟨(cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l).comp ρ,
    fun g m x hx => cyclotomicCharacter.spec l (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) x hx⟩

end GlobalTheory.MemLoc
