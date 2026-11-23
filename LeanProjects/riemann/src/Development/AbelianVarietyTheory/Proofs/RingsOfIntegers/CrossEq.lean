import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralExpansionUniqueOfUniformization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpFun

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ExpInt

theorem cross_eq {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    {L : LB G.left} (hL : L.IsLB) (k : ℕ) (σ σ' ρ ρ' : H0 L k)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))) (r r' : V)
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r))
    (h' : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r'))
    (hρ : SecIsMul G.hom r' ρ σ) (hρ' : SecIsMul G.hom r ρ' σ') : ρ = ρ' := by
  refine SecOps.sec_ext fun j => generic_app_injective G _ (fn_ext fun y hy => ?_)
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left)
    (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
  have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left) = j a := fun a => by
    rw [Subsingleton.elim a 0]; exact e ()
  have e₁ := secScal_sval h (𝟙 _) y hJ
  have e₂ := secScal_sval h' (𝟙 _) y hJ
  rw [sval_of σ _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₁
  rw [sval_of σ' _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₂
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
  refine (secIsMul_gs hρ _ y j hy).trans (Eq.trans ?_ (secIsMul_gs hρ' _ y j hy).symm)
  exact (congrArg _ e₁).trans ((mul_left_comm _ _ _).trans (congrArg _ e₂).symm)

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E E' : Fam D.toPre (FractionRing V) k), U.Expands k s E → U.Expands k s E' → E = E' := by
  intro hB V _ _ _ D A G _ _ U k s E E' hE hE'
  obtain ⟨r, hr, σ, f, h, hf, hx⟩ := hE
  obtain ⟨r', hr', σ', f', h', hf', hx'⟩ := hE'
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := G.hom) r' σ
  obtain ⟨ρ', hρ'⟩ := exists_secIsMul (p := G.hom) r σ'
  choose g hg using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r' (f α)
  choose g' hg' using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r (f' α)
  obtain rfl : ρ = ρ' := cross_eq G U.LG.isLB k σ σ' ρ ρ' s r r' h h' hρ hρ'
  obtain rfl : g = g' := GlobalTheory.ExpUniq.main hB V D A G U k ρ g g'
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ ρ f g hρ hg (hx e))
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ' ρ f' g' hρ' hg' (hx' e))
  refine fam_ext fun α j => sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
  have e₁ := secScal_sval (hf α) (𝟙 _) y hJ
  have e₁' := secScal_sval (hf' α) (𝟙 _) y hJ
  have e₂ : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg α) _ y _ (hJ.mem _ _)
  have e₂' : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f' α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg' α) _ y _ (hJ.mem _ _)
  rw [Category.assoc, Over.w] at e₂ e₂'
  rw [gs_scal] at e₁ e₁'
  rw [e₁] at e₂
  rw [e₁', e₂, mul_left_comm] at e₂'
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) ≫ jK V := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e₃] at e₂'
  exact (IsUnit.mul_right_inj (isUnit_cst _ y hr')).1 ((IsUnit.mul_right_inj (isUnit_cst _ y hr)).1 e₂')

end GlobalTheory.ExpFun
