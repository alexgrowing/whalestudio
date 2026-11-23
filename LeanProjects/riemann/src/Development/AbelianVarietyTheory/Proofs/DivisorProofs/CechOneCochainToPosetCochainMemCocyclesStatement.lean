import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocycles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toPos_mem_Z1_of_isCoc : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles <;> assumption)
