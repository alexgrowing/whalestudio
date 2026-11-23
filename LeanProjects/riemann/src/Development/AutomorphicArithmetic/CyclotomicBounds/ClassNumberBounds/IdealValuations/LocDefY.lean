import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs

open KStar.TotallyRealRoots

namespace KStar.IdealValuations

variable (l : ℕ) [Fact l.Prime]

def locInertia : Subgroup Gal(PadicAlgCl l/ℚ_[l]) where
  carrier := {g | ∀ (m : ℕ) (ζ : PadicAlgCl l), ¬ l ∣ m → ζ ^ m = 1 → g ζ = ζ}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := fun {g h} hg hh m ζ h1 h2 => by
    rw [AlgEquiv.mul_apply, hh m ζ h1 h2, hg m ζ h1 h2]
  inv_mem' := fun {g} hg m ζ h1 h2 => by
    conv_lhs => rw [← hg m ζ h1 h2]
    exact g.symm_apply_apply ζ

def IsResTrivial (g : Gal(PadicAlgCl l/ℚ_[l])) : Prop :=
  ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1

def IsLocFrob (σ : Gal(PadicAlgCl l/ℚ_[l])) : Prop :=
  ∀ (m : ℕ) (ζ : PadicAlgCl l), ¬ l ∣ m → ζ ^ m = 1 → σ ζ = ζ ^ l

noncomputable def unramField (k : ℕ) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  adjoinRoots ℚ_[l] (l ^ k - 1)

noncomputable def towerField (k s : ℕ) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  unramField l k ⊔ adjoinRoots ℚ_[l] (l ^ s)

variable {l} in

noncomputable def complField {E : Type*} [Field E] (j : E →+* PadicAlgCl l) :
    IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range j)

example : IsResTrivial l 1 := fun x _ => by simp

end KStar.IdealValuations
