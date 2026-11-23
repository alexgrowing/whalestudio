import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_model_ultrametric_points : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K] (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) → ∀ (y : Sp K ⟶ Xo.XF c) (b : c.V W₀ →+* W), y ≫ Y.j ≫ Y.s = spMap (algebraMap (FractionRing W) K) ≫ jK W ≫ spMap b → ∀ o : Full D C, FullAt Y (spMap gam ≫ y) o → ∃ (M : Mdl o) (f : W →+* M.W) (χ : Sp M.W ⟶ Y.X) (mp : SABMap M.t Y.t χ), f.Finite ∧ (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x)) ∧ jFK (R := M.W) C ≫ jK M.W ≫ χ = spMap gam ≫ y ≫ Y.j ∧ M.P.U.LG = M.t.PP := by
  first | exact @GlobalTheory.Ex.UnifModel.exists_mdl | exact GlobalTheory.Ex.UnifModel.exists_mdl | (intros; apply GlobalTheory.Ex.UnifModel.exists_mdl <;> assumption)
