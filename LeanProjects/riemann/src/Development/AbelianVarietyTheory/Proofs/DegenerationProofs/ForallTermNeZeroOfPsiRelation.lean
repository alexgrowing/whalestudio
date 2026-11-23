import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory

theorem psiRel_field_ne_zero_iff {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (s : Raw D F 1) (h : PsiRel D (TF (R := R) F) s) (χ : D.X) :
    (∃ j, (s χ).f j ≠ 0) ↔ ∃ j, (s 0).f j ≠ 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
  have := PsiExists.isIso_trF D F χ
  have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e := h χ (DegPre.BF D F) (fst _ _) κ (snd _ _) _ J hJ
  have e₁ : (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left = 𝟙 (DegPre.BF D F).left :=
    congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => q.left) lift_fst_snd
  have e₂ : sval (s χ) (𝟙 (DegPre.BF D F).left) (genericPoint _) J =
      (val (D.psi χ) κ.left (genericPoint _) J * rigV D (T := DegPre.BF D F) (genericPoint _) J).val *
        sval (s 0) (DegPre.trF D F χ).left (genericPoint _) J :=
    (congrArg (fun q => sval (s χ) q (genericPoint _) J) e₁).symm.trans e
  rw [exists_ne_zero_iff_sval_ne_zero _ hJ, e₂]
  constructor
  · intro h0
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact h0 (by rw [sval_eq_zero_of_local_eq_zero (s 0) hn _ _ J hJ, MulZeroClass.mul_zero])
  · intro h0
    exact mul_ne_zero (Units.ne_zero _) (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) h0 _ _ _ J hJ)

theorem forall_ne_zero_of_psiRel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  rintro R _ _ D f h ⟨α, hα⟩ β
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D (FractionRing R) (toUnit _) 1 f
  have h' := psiRel_of_pullB R D _ f s hs h
  have i := pullB_ne_zero_iff R D _ 1 f s hs
  exact (i β).1 ((psiRel_field_ne_zero_iff D _ s h' β).2 ((psiRel_field_ne_zero_iff D _ s h' α).1 ((i α).2 hα)))

end GlobalTheory
