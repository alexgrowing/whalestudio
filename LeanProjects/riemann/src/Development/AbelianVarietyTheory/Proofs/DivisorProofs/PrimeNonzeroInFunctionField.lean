import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

namespace GlobalTheory.Vert.Model

theorem natCast_prime_ne_zero_kbar : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] (B : GlobalTheory.Vert.Model O), ((p : ℕ) : Kbar B.X) ≠ 0 := by
  intro O _ _ _ p hp _ B
  have hpO : ((p : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h1 : B.const ((p : ℕ) : O) ≠ 0 := (B.isRegularFn_const hpO).ne_zero
  have hx : genericPoint B.X ∈ (⊤ : B.X.Opens) := trivial
  have h2 : (B.X.presheaf.germ ⊤ (genericPoint B.X) hx).hom (B.const ((p : ℕ) : O)) ≠ 0 := by
    intro h
    exact h1 ((germ_injective_of_isIntegral B.X (genericPoint B.X) hx) (h.trans (map_zero _).symm))
  have h3 : (algebraMap B.X.functionField (Kbar B.X))
      ((B.X.presheaf.germ ⊤ (genericPoint B.X) hx).hom (B.const ((p : ℕ) : O))) ≠ 0 :=
    (map_ne_zero _).2 h2
  simpa only [const, map_natCast] using h3

end GlobalTheory.Vert.Model
