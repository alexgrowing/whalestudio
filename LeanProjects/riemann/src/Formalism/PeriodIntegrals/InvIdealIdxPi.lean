import Mathlib

noncomputable section

namespace PI

open NumberField nonZeroDivisors

def InvIdealIdxPi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (J : ι → Ideal (𝓞 E)), (∀ i, J i ≠ ⊥) →
    (Submodule.pi Set.univ (fun _ : ι => (1 : Submodule (𝓞 E) E))).toAddSubgroup.relIndex
      (Submodule.pi Set.univ (fun i =>
        (((J i : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E))).toAddSubgroup =
      ∏ i, Ideal.absNorm (J i)

end PI

end
