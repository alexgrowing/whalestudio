import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefZeroInt

theorem coef_zero_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ th
  obtain ⟨lam, hlam, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) th
  refine ⟨lam, fun g b hb w x hx z J hJ => ?_⟩
  have h1 := hx z J hJ
  rw [pow_one] at h1
  rw [h1]
  have hs : sval (th.s 0) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (famProj D (FractionRing V) 1 0 th) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := rfl
  have hfst : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ famBase D (FractionRing V) = 𝟙 _ := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.prB D (FractionRing V)).left =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ b.left := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (snd (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_snd, hb, Over.comp_left]
  have hv : (Geo.Tor.val (g.s 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J).val = 1 := by
    rw [val_corr hJ g.s_zero, val_one]; rfl
  have e1 := sval_smul' (π := famBase D (FractionRing V)) hJ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left lam (termF D (FractionRing V) 1 0 θ)
  have e2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left hJ
  have hc : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs, hlam, e1, hfst]
  erw [e2]
  rw [hsnd, hv, _root_.mul_one, hc]

end GlobalTheory.UT.CoefZeroInt
