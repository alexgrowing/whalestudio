import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinCombValueAct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.ValuePullback

theorem valAt_abPull : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  intro R _ _ A F _ _ k t x fr x' fr' hx _ hv c h z J hJ
  obtain rfl : x' = GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x := Over.OverMorphism.ext hx
  let p : (TFK (R := R) F).left ⟶ (TFK (R := R) (FractionRing R)).left :=
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F).left
  have e : ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ≫
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A =
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ ptSecT A.A x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x)).left ≫
      (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A).left = p ≫ (ptSecT A.A x).left :=
    congrArg (fun q => q.left) e
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_
  rw [e']
  obtain ⟨hJ', h₁, -, -⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => (snd (TFK (R := R) (FractionRing R)) A.A).left) (fun _ => (k : ℤ)) (ptSecT A.A x).left p z J hJ
  obtain ⟨-, -, h₂, h₃⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => x.left) (fun _ => (k : ℤ)) (𝟙 _) p z J hJ
  refine (h₁ _).trans ((congrArg (p.stalkMap z).hom (h (p z) _ hJ')).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ?_)))
  · refine (h₃ _).symm.trans ?_
    rw [Category.comp_id]
    refine (gs_eq p z ⊤ trivial _).trans (Eq.trans ?_ (gs_eq (𝟙 _) z ⊤ trivial _).symm)
    refine congrArg _ ?_
    exact (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) F)))).symm
  · refine (h₂ _).symm.trans (congrArg Units.val ?_)
    rw [Category.comp_id]
    have p₁ : val (powFrame A.A A.L x fr k) p z J = val fr p z J ^ (k : ℤ) := map_zpow _ _ _
    have p₂ : val (powFrame A.A A.L _ fr' k) (𝟙 _) z J = val fr' (𝟙 _) z J ^ (k : ℤ) := map_zpow _ _ _
    exact p₁.trans ((congrArg (· ^ (k : ℤ)) (hv z J hJ).symm).trans p₂.symm)

end GlobalTheory.ValuePullback
