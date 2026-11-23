import Mathlib

universe u_1

namespace Bl.FirstLemmaO

noncomputable def goal1 :
  {A : Type u_1} → [inst : CommRing A] → {d : Nat} → Ideal A → Matrix (Fin d) (Fin d) A → Prop :=
  fun I M => ∀ i j, M i j ∈ I

end Bl.FirstLemmaO
