import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem comp_jFK_self : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
    jFK (R := R) (FractionRing R) = jFK (R := R) F := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = 𝟙 _ := Spec.map_id _
  exact (congrArg (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ ·) e).trans (Category.comp_id _)

noncomputable def toGen : TF (R := R) F ⟶ TF (R := R) (FractionRing R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK_self F)))

theorem toGen_jFK : (toGen (R := R) F).left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) F :=
  comp_jFK_self F

noncomputable def bc : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) :=
  lift (fst _ _ ≫ toGen F) (DegPre.prB D F)

theorem bc_fst : bc D F ≫ fst _ _ = fst _ _ ≫ toGen F := lift_fst _ _

theorem bc_prB : bc D F ≫ DegPre.prB D (FractionRing R) = DegPre.prB D F := lift_snd _ _

theorem bc_tr_prB (mu : D.X) :
    bc D F ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DegPre.trF D F mu ≫ DegPre.prB D F := by
  rw [trF_eq, trF_eq, tr_pr, tr_pr, MonObj.comp_mul, bc_prB, comp_cP, comp_cP, comp_cP]

theorem uVal_bc (k : ℕ) (α mu : D.X) (y : (DegPre.BF D F).left) (J) :
    uVal D (FractionRing R) k α (cP D _ mu) (bc D F) y J = uVal D F k α (cP D _ mu) (𝟙 _) y J := by
  rw [uVal, uVal, bc_prB, Category.id_comp, Category.id_comp, comp_cP, comp_cP, comp_cP]

theorem famMult_bc (k : ℕ) (α mu : D.X) (y : (DegPre.BF D F).left) {J} (hJ : Good D.P.L y J) :
    val (DegPre.famMult D (FractionRing R) k mu α) (bc D F ≫ fst _ _).left y J =
      val (DegPre.famMult D F k mu α) (𝟙 (DegPre.BF D F) ≫ fst _ _).left y J := by
  have e : (bc D F ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [bc_fst, Category.id_comp, Over.comp_left, Category.assoc, toGen_jFK]
  rw [val_famMult _ hJ, val_famMult _ hJ, e]

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (k : ℕ) (E : Fam D.toPre (FractionRing R) k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ θ : Fam D.toPre F k, ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1 := by
  intro hG R _ _ I D k E g hg F _ _
  have hL := D.toPre.P.isLB
  have e2 : ∀ χ, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (g χ) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun χ => by
    have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
        (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
      Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (g χ) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose t ht using e2
  refine ⟨⟨t, fun mu α u hu hc => ?_⟩, fun α => SectionScalarValuation.secScal_of_sval hL fun y J hJ => (ht α _ (𝟙 _) y J hJ).symm⟩
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e₃ := (gen_fe hG k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG k mu α
  have e₄ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (E.fe mu α u' hu' hc') _ (bc D.toPre F).left y J hJ
  rw [hv' u' hu' hc' _ (bc D.toPre F) y J hJ, uVal_bc, famMult_bc D.toPre F k α mu y hJ, ← e₃,
    ← SectionScalarValuation.secScal_sval (hg _) _ y hJ, ← SectionScalarValuation.secScal_sval (hg _) _ y hJ, ← Over.comp_left, bc_prB,
    Category.assoc, ← Over.comp_left, ← Over.comp_left, bc_tr_prB] at e₄
  rw [ht _ _ _ y J hJ, ht _ _ _ y J hJ, Category.id_comp, Category.id_comp]
  exact e₄

end GlobalTheory.FamBaseChange
