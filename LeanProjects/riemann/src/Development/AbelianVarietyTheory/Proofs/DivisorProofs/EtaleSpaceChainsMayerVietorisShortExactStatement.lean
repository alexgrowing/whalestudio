import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact : ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w, (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))) (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact := by
  first | (exact @GlobalTheory.EtC.mv_shortExact) | (exact GlobalTheory.EtC.mv_shortExact) | (intros; apply GlobalTheory.EtC.mv_shortExact  <;> assumption)
