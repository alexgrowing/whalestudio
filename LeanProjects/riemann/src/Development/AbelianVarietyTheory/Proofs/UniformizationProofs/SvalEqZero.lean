import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (gs_eq r z _ (hJ.mem φ r) _).trans ?_
  exact (congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → ∀ (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k), (∀ jj, s.f jj = 0) → U.Expands k s F → F = 0 := by
  intro R _ _ I D A G _ _ U k hR s F hs hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  obtain ⟨r, hr, σ, f, h₁, hf, hE⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ : ∀ j, σ.f j = 0 := fun j => by
    refine ExpInt.generic_app_injective G _ (Eq.trans (fn_ext fun y hy => ?_) (map_zero _).symm)
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y
      (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
    have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left) = j a := fun a => by
      rw [Subsingleton.elim a 0]; exact e ()
    have e₂ := ExpInt.secScal_sval h₁ (𝟙 _) y hJ
    rw [sval_eq_zero hs _ y hJ, mul_zero, sval_of σ _ y J j ej] at e₂
    refine ((gs_pull (𝟙 _) _ y _ hy _).trans e₂).trans ((gs_eq _ y _ hy _).trans ?_).symm
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hf0 : ∀ α j, (f α).f j = 0 := fun α => by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ f (fun j => ?_) (hE e) α j)
    exact (congrArg _ (hσ j)).trans (map_zero _)
  refine fam_ext fun α j => ?_
  refine sec_ext_val D.toPre.P.isLB (s' := SecOps.secZero) (fun y J hJ => ?_) j
  have e₁ := ExpInt.secScal_sval (hf α) (𝟙 _) y hJ
  rw [sval_eq_zero (hf0 α) _ y hJ, ExpInt.gs_scal] at e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing R)).hom =
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
  rw [e₃] at e₁
  refine Eq.trans ?_ (sval_eq_zero (fun _ => rfl) _ y hJ).symm
  exact (IsUnit.mul_right_eq_zero (ExpInt.isUnit_cst _ y hr)).1 e₁.symm

end GlobalTheory.ExpZero
