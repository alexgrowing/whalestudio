import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamFEOneOfPsiRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefInt

theorem coef_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (lam : FractionRing V) (th : Fam D (FractionRing V) 1),
    famProj D (FractionRing V) 1 0 th = lam • termF D (FractionRing V) 1 0 θ →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (χ : D.X) (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b →
    ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w χ (th.s χ) x →
    ∀ z J, Good D.P.L z J →
      cst (FractionRing V) z x = cst (FractionRing V) z lam *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi χ) (jFK (R := V) (FractionRing V)) z J)).val *
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
          ((toUnit (TF (R := V) (FractionRing V))).left ≫ (b * D.c χ).left) z J *
        (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ lam th hlam hrig χ g b hb w x hx z J hJ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have h1 := hx z J hJ
  rw [pow_one] at h1
  obtain ⟨u, hu, hc, hrel⟩ := fe_from_zero hG D (FractionRing V) th χ
  have e1 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J hJ
  have e2 := (gen_fe (D := D) (F := FractionRing V) hG 1 χ 0).2 u hu hc _ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b) z J hJ
  rw [GlobalTheory.UU.uVal_one D _ _ _ _ hJ, _root_.one_mul, lift_fst, Over.id_left] at e2
  have e3 := GlobalTheory.UU.val_famMult_one D (FractionRing V) (𝟙 (TF (R := V) (FractionRing V))) hJ χ 0
  have hps : val (D.psi (χ + 0)) (jFK (R := V) (FractionRing V)) z J = val (D.psi χ) (jFK (R := V) (FractionRing V)) z J := by
    rw [add_zero]
  rw [Over.id_left, Category.id_comp, hps] at e3
  have e4 := hrig _ (jFK (R := V) (FractionRing V)) z J hJ
  have hrK : val D.rigK (jFK (R := V) (FractionRing V)) z J = rigV D (TF (R := V) (FractionRing V)).hom z J := by
    rw [DegPre.rigK, val_pull hJ]
    rfl

  have hfm : val (DegPre.famMult D (FractionRing V) 1 χ 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J =
      val (D.psi χ) (jFK (R := V) (FractionRing V)) z J * val D.rigK (jFK (R := V) (FractionRing V)) z J := by
    have h0 : val (D.psi 0) (jFK (R := V) (FractionRing V)) z J = (val D.rigK (jFK (R := V) (FractionRing V)) z J)⁻¹ :=
      eq_inv_of_mul_eq_one_left e4
    rw [h0] at e3
    exact eq_mul_of_mul_inv_eq e3
  have hsχ : sval (th.s χ) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (th.s (0 + 1 • χ)) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := by
    rw [zero_add, one_smul]
  have hfst : ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) ≫
      famBase D (FractionRing V) = 𝟙 _ := by
    show _ ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, DegPre.trF, lift_fst, lift_fst]; rfl
  have hsndO : lift (𝟙 (TF (R := V) (FractionRing V))) g.b ≫ DegPre.trF D (FractionRing V) χ ≫ DegPre.prB D (FractionRing V) =
      toUnit _ ≫ (b * D.c χ) := by
    rw [ReciprocityTheory.ChartRestriction.G.DVR.trF_eq, ReciprocityTheory.ChartRestriction.G.DVR.tr_pr, MonObj.comp_mul, ← Category.assoc, lift_fst, Category.id_comp,
      lift_snd, hb, MonObj.comp_mul]
    rfl
  have hsnd : ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) ≫
      (DegPre.prB D (FractionRing V)).left = (toUnit (TF (R := V) (FractionRing V))).left ≫ (b * D.c χ).left := by
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hsndO]
  have hs0 : sval (th.s 0) ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) z J =
      sval (famProj D (FractionRing V) 1 0 th) ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫
        (DegPre.trF D (FractionRing V) χ).left) z J := rfl
  have t1 := sval_smul' (π := famBase D (FractionRing V)) hJ
    ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) lam
    (termF D (FractionRing V) 1 0 θ)
  have t2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ
    ((lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.trF D (FractionRing V) χ).left) hJ
  have hc0 : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs0, hlam, t1, hfst, hc0] at e1
  erw [t2] at e1
  rw [hsnd] at e1
  rw [hsχ, e1, e2, hfm, hrK] at h1
  refine (Units.mul_left_inj (rigV D (TF (R := V) (FractionRing V)).hom z J)).1 (h1.trans ?_)
  simp only [Units.val_mul, id]
  ring

end GlobalTheory.UT.CoefInt
