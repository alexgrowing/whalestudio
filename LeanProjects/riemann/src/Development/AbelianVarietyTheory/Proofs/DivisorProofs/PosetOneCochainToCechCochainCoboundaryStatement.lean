import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetOneCochainToCechCochainCoboundary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCob_toCech_d0 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  first | exact @GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | exact GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | (intros; apply GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary <;> assumption)
