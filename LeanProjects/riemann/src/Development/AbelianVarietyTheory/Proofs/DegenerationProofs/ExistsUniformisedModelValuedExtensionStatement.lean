import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModelValuedExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedModel_valued_extension : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] (A : Lift a K) (o : Full D K), o.ρ = A.ρ → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K₁ : Type) [Field K₁] [Algebra (FractionRing W) K₁] [Algebra.IsAlgebraic (FractionRing W) K₁] (gam : K₁ →+* C) (e : K →+* K₁) (φ : O' →+* W), (∀ x, gam (algebraMap (FractionRing W) K₁ x) = algebraMap (FractionRing W) C x) → (∀ x, e (algebraMap (FractionRing O') K (algebraMap O' _ x)) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x))) → ∀ o' : Full D C, FullExt (gam.comp e) o o' → ∃ (M : Mdl o') (f : W →+* M.W), ∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x) := by
  first | exact @GlobalTheory.Ex.ExtModel.exists_mdl_ext | exact GlobalTheory.Ex.ExtModel.exists_mdl_ext | (intros; apply GlobalTheory.Ex.ExtModel.exists_mdl_ext <;> assumption)
