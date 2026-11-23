import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCover
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), (∀ s, Injective (I.X s)) → (∀ s, Injective (J.X s)) → ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) I n a = 0 → cpull ((chains R).map g) J m b = 0 → μ.cup E hk a b = 0 := by
  first | (exact @GlobalTheory.EtC.cup_supp) | (exact GlobalTheory.EtC.cup_supp) | (intros; apply GlobalTheory.EtC.cup_supp  <;> assumption)
