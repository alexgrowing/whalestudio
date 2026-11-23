import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_twistedConj_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → twOrb θ K (g⁻¹ * δ * θ g) f = twOrb θ K δ f := by
  first | exact @GlobalTheory.TwOrbConj.twOrb_twConj | exact GlobalTheory.TwOrbConj.twOrb_twConj | (intros; apply GlobalTheory.TwOrbConj.twOrb_twConj <;> assumption)
