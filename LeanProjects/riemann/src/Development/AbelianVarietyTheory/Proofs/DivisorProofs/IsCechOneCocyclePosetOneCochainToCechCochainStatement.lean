import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) := by
  first | exact @GlobalTheory.CechCmp.isCoc_toCech | exact GlobalTheory.CechCmp.isCoc_toCech | (intros; apply GlobalTheory.CechCmp.isCoc_toCech <;> assumption)
