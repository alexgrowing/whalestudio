import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEtaleCoverListingHeckeKernelScheme
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_cover_listing_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk), ∃ (T' : Type) (_ : CommRing T') (_ : Algebra T T') (n : ℕ) (σ : Fin n → (Sp T' ⟶ Xo.univ.t.G.left)), Algebra.Etale T T' ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap T T')) ∧ (∀ j, σ j ≫ Xo.univ.t.G.hom = spMap (algebraMap T T') ≫ h ≫ Z.π₁) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T' →+* Ω) (x₁ : Sp Ω ⟶ Xo.X) (C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)), Z.Carries (spMap χ ≫ spMap (algebraMap T T') ≫ h) x₁ C → ∃ e : Fin n ≃ C, ∀ j, (e j).1.left = spMap χ ≫ σ j := by
  first | exact @GlobalTheory.HeckeEx.exists_etale_cover_lists_kerScheme | exact GlobalTheory.HeckeEx.exists_etale_cover_lists_kerScheme | (intros; apply GlobalTheory.HeckeEx.exists_etale_cover_lists_kerScheme <;> assumption)
