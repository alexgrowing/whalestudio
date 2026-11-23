import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSpecProdBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_specProd_bijective : ∀ (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] (F : Shv R), Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) => (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s, Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s) := by
  first | exact @GlobalTheory.EtC.sec_prod | exact GlobalTheory.EtC.sec_prod | (intros; apply GlobalTheory.EtC.sec_prod <;> assumption)
