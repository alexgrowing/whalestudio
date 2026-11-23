import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

open GlobalTheory.HodgeTateCompare in

theorem omega_free_finite_bijective_of_smooth {O : Type} [CommRing O] [IsLocalRing O]
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [Smooth G.hom] :
    Module.Free O (omega G) ∧ Module.Finite O (omega G) ∧
      Function.Bijective (fun (x : LieG G) => ((LinearMap.proj x : (LieG G → O) →ₗ[O] O) ∘ₗ
        (omega G).subtype : Module.Dual O (omega G))) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  haveI : Module.Free O (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) := Module.free_of_flat_of_isLocalRing
  refine ⟨.of_equiv (omegaEquiv G), .equiv (omegaEquiv G), ?_⟩
  refine (Function.Bijective.of_comp_iff _ (lieEquiv G).bijective).1 ?_
  refine (Function.Bijective.of_comp_iff' (omegaEquiv G).dualMap.bijective _).1 ?_
  convert Function.bijective_id
  funext w
  exact LinearMap.ext fun f => ev_apply f w

theorem Point.omega_free_finite_bijective : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Module.Free O (omega P.Gt) ∧ Module.Finite O (omega P.Gt) ∧ Function.Bijective (fun (x : LieG P.Gt) => ((LinearMap.proj x : (LieG P.Gt → O) →ₗ[O] O) ∘ₗ (omega P.Gt).subtype : Module.Dual O (omega P.Gt))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  haveI := P.isLocalRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  exact omega_free_finite_bijective_of_smooth P.Gt

end GlobalTheory.HTLat
