import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_productGroup : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → (∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite → {q : DoubleCoset.Quotient (twCent θ' δ' : Set G') (K' : Set G') | ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * δ' * θ' (Quotient.out q * k)) ≠ 0}.Finite → twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  first | exact @GlobalTheory.BCT.OrbProd.twOrb_prod | exact GlobalTheory.BCT.OrbProd.twOrb_prod | (intros; apply GlobalTheory.BCT.OrbProd.twOrb_prod <;> assumption)
