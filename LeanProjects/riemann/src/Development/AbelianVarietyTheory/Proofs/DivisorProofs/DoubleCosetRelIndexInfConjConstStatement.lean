import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConst
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_relIndex_inf_conj_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  first | exact @GlobalTheory.doubleCoset_relIndex_const | exact GlobalTheory.doubleCoset_relIndex_const | (intros; apply GlobalTheory.doubleCoset_relIndex_const <;> assumption)
