import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmpleAlongPullback_transport_iso : ∀ {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn], gn ≫ pA = p → ∀ (π : Y ⟶ X) {L : LB X}, L.IsLB → ∀ {LA : LB XA}, LA.IsLB → ∀ {k m : ℕ} (b : Fin (m + 1) → H0 LA k), VeryAmpleAlong pA (𝟙 XA) LA b → ∀ (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ), (∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) → ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j = u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) → VeryAmpleAlong p π L σ := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_transport | exact GlobalTheory.Mum.veryAmpleAlong_transport | (intros; apply GlobalTheory.Mum.veryAmpleAlong_transport <;> assumption)
