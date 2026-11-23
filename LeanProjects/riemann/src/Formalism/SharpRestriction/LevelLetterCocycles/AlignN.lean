import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def tameList {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Option (Fin m × Bool) → (ZMod g)ˣ
  | none => 1
  | some (j, true) => χ j
  | some (j, false) => (χ j)⁻¹

def TameDistinct (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Prop :=
  Function.Injective (tameList χ) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB r g →
    Function.Injective (fun o => Formalism.CyclotomicNorms.primeToPart ℓ
      (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((tameList χ o : (ZMod g)ˣ) : ZMod g)))) ∧
  ∀ j, IsSquare (χ j)

def TameDistinctF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (k : Fin 2) (v : (Fm.D x i).nd.PlG k),
    haveI : Fact ((Fm.D x i).host.g k).Prime := ⟨(Fm.D x i).host.g_prime k⟩
    TameDistinct (Fm.D x i).R.r ((Fm.D x i).host.g k) ((Fm.D x i).nd.chiT k v)

end Formalism.MainNotions
