import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.RefPull

open GlobalTheory.HalfBC

theorem refines_pull : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  intro V V₀ V₁ _ _ _ _ _ _ Q ρ₀ D₀ e₀ hρ₀ H ρ D₁ hD hρ
  obtain ⟨β₀, β₂₀, w₀, pb₀, sq₀, gen₀, c₀, tau₀⟩ := H
  have gp := pull_grp hD
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  have hΛ₁ : (abelian₂ D₁.P.A D₁.P.L).IsLB := DVR.linComb_isLB _ D₁.P.isLB _ _
  obtain ⟨w', T⟩ := exists_comp hΛ₀ w₀ (lamIso gp hD.w) ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen)) hΛQ hΛ₁
  set β : D₁.P.A.left ⟶ D₀.P.A.left := hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf ρ) with hβ
  let gam : FractionRing V₀ →+* FractionRing V₁ := GlobalTheory.ArcPull.fracMap hρ
  have hgam : ∀ r, gam (algebraMap V₀ _ r) = algebraMap V₁ _ (ρ r) := GlobalTheory.ArcPull.fracMap_algebraMap hρ
  have sgam := gam_comm ρ gam hgam
  obtain ⟨κ₁, hκ₁, hκu⟩ := exists_kappa ρ₀ ρ gam hgam hρ₀
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D₁.P.A).left) (z : Z) J J₁ J', Good Q.M.L z J → Good D₀.P.L z J₁ →
      Good D₁.P.L z J' → lamVal w' p z J J' = lamVal w₀ (p ≫ sqOf gp) z J J₁ *
        ∏ I, gw hD.w (p ≫ lamφ D₁.P.A I) z (J₁ ((p ≫ lamφ D₁.P.A I) ≫ β)) (J' (p ≫ lamφ D₁.P.A I)) ^ lamε I := by
    intro Z p z J J₁ J' hJ hJ₁ hJ'
    have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)) (fun I => J' (p ≫ lamφ D₁.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D₁.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw w₀ (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂₀ ≫ lamφ Q.B I))
        (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      simp only [Category.assoc]
    · rw [gw_lamIso gp hD.w p z _ _ (fun I => by
        have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)
        rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
        exact this) (fun I => hJ' (p ≫ lamφ D₁.P.A I))]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc]
  refine ⟨β ≫ β₀, sqOf gp ≫ β₂₀, w', ?_, ⟨?_, ?_⟩, (isGen_iff _).2 (T.pgen_comp hΛ₀ ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen))), ?_, ?_⟩
  · exact (IsGrpPullback.comp gp pb₀).congr (spMap_comp_spMap' ρ₀ ρ) rfl
  · rw [Category.assoc, sq₀.1, ← Category.assoc, (isSquare_sqOf gp).1, Category.assoc]
  · rw [Category.assoc, sq₀.2, ← Category.assoc, (isSquare_sqOf gp).2, Category.assoc]
  · intro a
    show (D₁.c a).left ≫ β ≫ β₀ = spMap (ρ.comp ρ₀) ≫ (Q.c (e₀ (hD.xe a))).left
    rw [← Category.assoc, hβ, hD.c_pr, Category.assoc, c₀, ← Category.assoc, spMap_comp_spMap']
  · intro κ hκ a b z J J' hJ hJ'
    obtain rfl := hκu κ hκ
    choose J₁ hJ₀ using fun χ : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (χ z)
    have hJ₁ : Good D₀.P.L z J₁ := hJ₀
    let g₀ : (TK V₁).left ⟶ (TK V₀).left := spMap gam
    have hx : ∀ χ, D₁.xK χ ≫ β = g₀ ≫ D₀.xK (hD.xe χ) := fun χ => by
      show (jK V₁ ≫ (D₁.c χ).left) ≫ β = spMap gam ≫ jK V₀ ≫ (D₀.c (hD.xe χ)).left
      rw [Category.assoc, hβ, hD.c_pr, ← Category.assoc, ← sgam, Category.assoc]
    have hP : (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left ≫ sqOf gp =
        g₀ ≫ (lift (toUnit (TK V₀) ≫ D₀.c (hD.xe a)) (toUnit (TK V₀) ≫ D₀.c (hD.xe b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst D₀.P.A D₀.P.A).left = _ ≫ (fst D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact hx a
      · show _ ≫ (snd D₀.P.A D₀.P.A).left = _ ≫ (snd D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact hx b
    have t₁ := tau₀ κ₁ hκ₁ (hD.xe a) (hD.xe b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (D₀.tau (hD.xe a) (hD.xe b)) (g₀ ≫ 𝟙 _) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D₀.tau (hD.xe a) (hD.xe b)) (𝟙 _) (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J₁ hJ₁).2.2.1 _)
    have nQ : val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (g₀ ≫ κ₁) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) κ₁ (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κ₁ g₀ z J hJ).2.2.1 _)
    rw [Category.comp_id] at n₁
    have A := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp w₀ g₀ _ z J J₁ hJ hJ₁).symm nQ.symm))
    let h : ((TK V₁).left ⟶ D₁.P.A.left) → ((TK V₁).left.presheaf.stalk z)ˣ :=
      fun q => gw hD.w q z (J₁ (q ≫ β)) (J' q)
    have tv := GlobalTheory.ArcPull.tau_val hD g₀ (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' a b
    have K := (key _ (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
      (congrArg₂ (· * ·) (congrArg (fun q => lamVal w₀ q z J J₁) hP)
        (prod_lam (DVR.cP D₁ (TK V₁) a) (DVR.cP D₁ (TK V₁) b) h))
    have o₀ : ∀ x, h (DVR.cP D₁ (TK V₁) x).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (D₁.xK x) := fun _ => rfl
    have o₁ : h (1 : TK V₁ ⟶ D₁.P.A).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (1 : TK V₁ ⟶ D₁.P.A).left := rfl
    rw [← DVR.cPoint_add] at K
    simp only [o₀, o₁] at K
    simp only [Category.id_comp] at tv
    rw [K]
    show _ = _ * val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (spMap gam ≫ κ₁) z J
    apply Additive.ofMul.injective
    have eA := congrArg Additive.ofMul A
    have eT := congrArg Additive.ofMul tv
    simp only [ofMul_mul, ofMul_inv] at eA eT ⊢
    linear_combination (norm := abel) eA - eT

end GlobalTheory.RefPull
