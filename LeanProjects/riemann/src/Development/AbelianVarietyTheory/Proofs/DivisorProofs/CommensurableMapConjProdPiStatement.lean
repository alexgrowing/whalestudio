import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableMapConjProdPi
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurable_map_conj_prod_pi' : ∀ {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)] (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)), Subgroup.Commensurable (H.map (MulAut.conj g.1).toMonoidHom) H → (∀ i, Subgroup.Commensurable ((K i).map (MulAut.conj (g.2 i)).toMonoidHom) (K i)) → Subgroup.Commensurable ((H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom) (H.prod (Subgroup.pi Set.univ K)) := by
  first | (exact @GlobalTheory.commensurable_map_conj_prod_pi) | (exact GlobalTheory.commensurable_map_conj_prod_pi) | (intros; apply GlobalTheory.commensurable_map_conj_prod_pi  <;> assumption)
