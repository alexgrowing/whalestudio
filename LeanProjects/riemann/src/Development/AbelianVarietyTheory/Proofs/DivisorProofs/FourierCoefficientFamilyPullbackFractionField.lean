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
namespace GlobalTheory.Poinc.Tors.CoefPull

open GlobalTheory.FieldBaseChange GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EvalZero

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem cst_map (z : (TF (R := R) F).left) (a : E) :
    cst (R := R) F z (algebraMap E F a) =
      ((baseMap (R := R) E F).left.stalkMap z).hom (cst (R := R) E ((baseMap (R := R) E F).left z) a) := by
  refine Eq.trans ?_ (gs_comp_stalkMap (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _)
  rw [Category.comp_id]
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (baseMap (R := R) E F).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 _) z ⊤) ?_
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap E F)))

theorem coef_famPull (hf : (algebraMap E F).comp (algebraMap (FractionRing R) E) = algebraMap (FractionRing R) F)
    (hG : GlobalFnsSt) (k : ℕ) (s : Fam D E k) (g : GtPtF D E) (w : Frm D E k g.b)
    (w' : Frm D F k (gtExt D (algebraMap E F) hf g).b) (hw : w.IsGen)
    (hv : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap E F)) z J) (χ : D.X) :
    coef (famPull D E F hG k s) (gtExt D (algebraMap E F) hf g) w' χ = algebraMap E F (coef s g w χ) := by
  refine coef_eq fun z J hJ => ?_
  let p := baseMap (R := R) E F
  have hJ' : Good D.P.L (p.left z) (fun ψ => J (p.left ≫ ψ)) := fun ψ => hJ (p.left ≫ ψ)
  have a := congrArg (p.left.stalkMap z).hom (isCoef_coef g hw χ s (p.left z) _ hJ')
  rw [map_mul, map_mul, map_mul, map_pow] at a
  have hb : (gtExt D (algebraMap E F) hf g).b = p ≫ g.b := gtExt_b _ hf g
  have e : lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b ≫ famMap D E F = p ≫ lift (𝟙 _) g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, famMap_fst, lift_fst_assoc, Category.assoc, lift_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, lift_snd, ← hb]
      exact (congrArg _ (famMap_snd D E F)).trans (lift_snd _ _)
  have e' : (lift (𝟙 (TF (R := R) F)) (gtExt D (algebraMap E F) hf g).b).left ≫ (famMap D E F).left =
      p.left ≫ (lift (𝟙 _) g.b).left := congrArg (fun q => q.left) e
  refine (congrArg₂ (· * ·) (cst_map z _) (congrArg (· ^ k) ?_)).trans (a.trans
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_).symm)
  · exact val_comp_map (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig p.left
      (TF (R := R) E).hom _ (Over.w p) z hJ
  · refine (sval_pullOver _ _ _ _ hJ).trans ?_
    refine Eq.trans (by rw [e']) ?_
    exact (values_natural _ _ _ _ D.P.L _ _ _ _ p.left z J hJ).2.1 (s.s χ)
  · exact (congrArg Units.val (gtExt_val _ hf g χ hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)
  · exact (congrArg Units.val (hv z J hJ)).trans (val_comp_map _ p.left (𝟙 _) _ (Category.comp_id _) z hJ)

theorem coef_famPull_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b) (w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b), w.IsGen → w'.IsGen → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap (FractionRing R) F)) z J) → ∀ χ : D.X, coef (GlobalTheory.FieldBaseChange.famPull D (FractionRing R) F hG k s) (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' χ = algebraMap (FractionRing R) F (coef s g w χ) :=
  fun _ _ _ _ _ _ _ hG k s g w w' hw _ hv χ => coef_famPull _ hG k s g w w' hw hv χ

end GlobalTheory.Poinc.Tors.CoefPull
end
