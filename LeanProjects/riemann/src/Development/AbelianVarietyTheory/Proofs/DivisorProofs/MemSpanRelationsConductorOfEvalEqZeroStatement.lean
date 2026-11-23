import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero : ∀ (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E] (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D) (F : σ → MvPolynomial ν R), Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) → RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) → IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) → ∀ G : MvPolynomial ν R', MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0 → G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  first | exact @GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | exact GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | (intros; apply GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero <;> assumption)
