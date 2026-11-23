import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ), Function.Bijective (fun x : Ht q (sp (A × B)) n i => (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  first | (exact @GlobalTheory.EtC.ProdCoh.ht_prod_bijective) | (exact GlobalTheory.EtC.ProdCoh.ht_prod_bijective) | (intros; apply GlobalTheory.EtC.ProdCoh.ht_prod_bijective  <;> assumption)
