import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamFEOneOfPsiRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntTerm

open GlobalTheory.Poinc.ThetaOne in

theorem coef_eq_theta_value : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ₀ : FractionRing V, ∀ (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b), w.IsGen → ∀ (mu : D.X) (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z (coef s g' w mu) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z κ₀ * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ s
  obtain ⟨κ₀, hκ, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) s
  refine ⟨κ₀, fun g' w hw mu z J hJ => ?_⟩
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let ρ : TF (R := V) (FractionRing V) ⟶ DegPre.BF D (FractionRing V) := lift (𝟙 _) g'.b
  have hρ₁ : ρ ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have hρ₂ : ρ ≫ DegPre.prB D (FractionRing V) = g'.b := lift_snd _ _

  have s0 : ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ (DegPre.BF D (FractionRing V)).left),
      sval (s.s 0) r z J = GlobalTheory.FieldBaseChange.constVal (r ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V)) z κ₀ *
        sval θ (r ≫ (DegPre.prB D (FractionRing V)).left) z J := by
    intro r
    have h1 : (GlobalTheory.FieldBaseChange.famProj D (FractionRing V) 1 0 s) = κ₀ • termF D (FractionRing V) 1 0 θ := hκ
    have h2 := congrArg (fun t : GlobalTheory.FieldBaseChange.FamTerm D (FractionRing V) 1 0 => sval (L := D.P.L) t r z J) h1
    refine h2.trans ?_
    rw [GlobalTheory.FieldBaseChange.sval_smul' hJ]
    congr 1
    exact GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ
  have key : ∀ x, x = 0 + 1 • mu →
      GlobalTheory.UT.cst (FractionRing V) z (coef s g' w x) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val =
      GlobalTheory.UT.cst (FractionRing V) z κ₀ *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val *
        sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s x) (𝟙 _) z J).val *
        (Geo.Tor.val w (𝟙 _) z J).val := by
    rintro x rfl
    have a := GlobalTheory.UT.CoefBasic.isCoef_coef g' hw (0 + 1 • mu) s z J hJ
    rw [pow_one] at a
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := FractionRing V) hG 1 mu 0
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu 0 u hu hc) _ ρ.left z J hJ
    have v := hv u hu hc _ ρ z J hJ
    rw [GlobalTheory.UU.uVal_one D (FractionRing V) _ _ _ hJ, _root_.one_mul, hρ₁] at v
    have m := GlobalTheory.UU.val_famMult_one D (FractionRing V) (𝟙 _) hJ mu 0
    rw [Over.id_left, Category.id_comp] at m
    have m' := congrArg Units.val m
    rw [Units.val_mul] at m'
    have ps : ∀ y, y = mu → (Geo.Tor.val (D.psi y) (jFK (R := V) (FractionRing V)) z J).val =
        (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val := by
      rintro _ rfl; rfl
    rw [ps _ (add_zero mu)] at m'
    have b₁ : ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V) = 𝟙 _ := by
      rw [GlobalTheory.FieldBaseChange.trF_famBase]
      exact congrArg (fun q => q.left) hρ₁
    have b₂ : (ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left) ≫ (DegPre.prB D (FractionRing V)).left =
        (padd D.P.A (DegPre.cT D _ mu) g'.b).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, DegPre.trF, lift_snd,
        GlobalTheory.IntFam.TermLift.comp_padd, hρ₂, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
      exact congrArg (fun q => Over.Hom.left q)
        (show padd D.P.A g'.b (DegPre.cT D _ mu) = padd D.P.A (DegPre.cT D _ mu) g'.b from mul_comm _ _)
    rw [s0, Category.assoc, b₁, b₂] at e
    rw [a, e, v]
    have c₀ : GlobalTheory.FieldBaseChange.constVal (𝟙 (TF (R := V) (FractionRing V)).left) z κ₀ = GlobalTheory.UT.cst (FractionRing V) z κ₀ := rfl
    rw [c₀]
    simp only [id]
    linear_combination (GlobalTheory.UT.cst (FractionRing V) z κ₀ * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J *
      (Geo.Tor.val (g'.s (0 + 1 • mu)) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val) * m'
  have := key mu (by rw [zero_add, one_smul])
  exact this

end GlobalTheory.Poinc.IntTerm
end
