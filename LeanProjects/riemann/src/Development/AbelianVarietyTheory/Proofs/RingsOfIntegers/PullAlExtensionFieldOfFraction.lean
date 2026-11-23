import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section

variable (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem jFK_self : jFK (R := V) (FractionRing V) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
  exact Spec.map_id _

def specFrac : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing V)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F))

theorem specFrac_jFK : specFrac V F ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  (congrArg (fun q => specFrac V F ≫ q) (jFK_self V)).trans (Category.comp_id _)

def toFrac : TF (R := V) F ⟶ TF (R := V) (FractionRing V) :=
  Over.homMk (specFrac V F) ((Category.assoc (specFrac V F) (jFK (R := V) (FractionRing V)) (jK V)).symm.trans
    (congrArg (fun q => q ≫ jK V) (specFrac_jFK V F)))

theorem toFrac_jFK : (toFrac V F).left ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  specFrac_jFK V F

variable {V} (D : DegPre V)

def bc : DegPre.BF D F ⟶ DegPre.BF D (FractionRing V) := toFrac V F ▷ D.P.A

theorem bc_prB : bc F D ≫ DegPre.prB D (FractionRing V) = DegPre.prB D F := whiskerRight_snd _ _

theorem bc_prB_left : (bc F D).left ≫ (DegPre.prB D (FractionRing V)).left = (DegPre.prB D F).left :=
  congrArg (fun q => q.left) (bc_prB F D)

theorem zF_bc : DegPre.zF D F ≫ bc F D = toFrac V F ≫ DegPre.zF D (FractionRing V) := by
  unfold DegPre.zF bc
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, whiskerRight_snd, lift_snd]
    rw [← Category.assoc, comp_toUnit]

theorem bc_famφ (α : D.X) (i : Fin 4) :
    (bc F D).left ≫ DegPre.famφ D (FractionRing V) α i = DegPre.famφ D F α i := by
  rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, bc_prB_left]

end

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (F : Type) [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_bc (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ bc F D.toPre = bc F D.toPre ≫ aF D (FractionRing V) oa a := by
  unfold aF
  apply CartesianMonoidalCategory.hom_ext
  · simp [bc]
  · simp only [Category.assoc, lift_snd]
    rw [← Category.assoc (bc F D.toPre), bc_prB]
    exact lift_snd _ _

theorem aF_bc_left (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (bc F D.toPre).left = (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left :=
  congrArg (fun q => q.left) (aF_bc D F oa a)

theorem bc_pullφ (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) (i : Fin 4 ⊕ Fin 4) :
    (bc F D.toPre).left ≫ pullφ D (FractionRing V) oa a χ i = pullφ D F oa a χ i := by
  rcases i with i | i
  · exact bc_famφ F D.toPre _ i
  · show (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left ≫ _ = (aF D F oa a).left ≫ _
    rw [← Category.assoc, ← aF_bc_left, Category.assoc, bc_famφ]

theorem sval_bc {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {g : D.toPre.SecB k α}
    (hs : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1)
    (ht : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) t (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval t r z J = sval s (r ≫ (bc F D.toPre).left) z J := by
  rw [← SectionScalarValuation.secScal_sval ht r z hJ, ← SectionScalarValuation.secScal_sval hs _ z hJ, Category.assoc, bc_prB_left]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (E : Fam D.toPre (FractionRing V) k) (E' : Fam D.toPre (FractionRing V) (k * N)) (g : ∀ α, D.toPre.SecB k α) (g' : ∀ α, D.toPre.SecB (k * N) α) (θ : Fam D.toPre F k) (θ' : Fam D.toPre F (k * N)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (E'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (θ'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre F).left 1) → PullAl D (FractionRing V) oa a k N E E' → PullAl D F oa a k N θ θ' := by
  intro V _ _ _ D F _ _ O _ _ _ oa a k N E E' g g' θ θ' hE hE' hθ hθ' hP
  have hL := D.toPre.P.isLB
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hrel⟩ := hP.1 χ
    obtain ⟨u', hu', vu⟩ := exists_gen hL (φ' := pullφ D F oa a χ) (ε' := pullε k N)
      (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [bc_pullφ])
      (LB.pullGen D.toPre.P.L _ _ u (bc F D.toPre).left) (pullGen_isGen _ _ _ _ hu _)
    refine ⟨u', hu', corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_⟩
    · have e := val_corr hJ hc (toFrac V F).left
      rw [val_pull hJ, val_pull hJ, toFrac_jFK] at e
      have z₁ : (DegPre.zF D.toPre F).left ≫ (bc F D.toPre).left =
          (toFrac V F).left ≫ (DegPre.zF D.toPre (FractionRing V)).left :=
        congrArg (fun q => q.left) (zF_bc F D.toPre)
      rw [val_pull hJ, val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, Category.id_comp, z₁]
      exact e
    · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (bc F D.toPre).left y J hJ
      rw [sval_bc D F (hE' _) (hθ' _) _ y hJ, sval_bc D F (hE _) (hθ _) _ y hJ, vu _ _ y J hJ, val_pull hJ,
        Category.id_comp, Category.id_comp, aF_bc_left]
      exact e
  · refine fn_ext (V := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F β) j) fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left => exists_chart hL (ψ y)
    have hI' : Good D.toPre.P.L y I := hI
    have e : sval (θ'.s β) (𝟙 _) y I = 0 := by
      rw [sval_bc D F (hE' β) (hθ' β) _ y hI']
      exact (congrArg (gs _ y _) (hP.2 β hβ _)).trans (gs_zero _ y _ (hI'.mem _ _))
    refine (sec_trans (θ'.s β) (𝟙 _) y hy (hI'.mem _ _)).trans ?_
    exact (congrArg _ e).trans ((mul_zero _).trans (gs_zero _ y _ hy).symm)

end GlobalTheory.PullBaseChange
