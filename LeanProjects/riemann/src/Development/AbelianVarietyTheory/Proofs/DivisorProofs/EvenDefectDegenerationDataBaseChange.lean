import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenDescendBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (y : Sp B) :
    gm (spMap f) y ⊤ (unitOn u) = gm (𝟙 (Sp B)) y ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  apply Units.ext
  rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial]
  have nat := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact congrArg ((Sp B).presheaf.germ ⊤ y trivial).hom nat.symm

theorem evenDefect_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  intro R₁ _ _ R₂ _ _ σ D₁ D₂ β v xe gam hgam gp hv hc _ hψ h hE χ z J₂ hJ₂
  beta_reduce
  have hgam' : spMap gam ≫ jK R₁ = jK R₂ ≫ spMap σ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hgam
  have cx : ∀ a, D₂.xK a ≫ β = spMap gam ≫ D₁.xK (xe a) := fun a => by
    show (jK R₂ ≫ (D₂.c a).left) ≫ β = spMap gam ≫ jK R₁ ≫ (D₁.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam', Category.assoc]
  have cn : D₂.xK (-χ) = D₂.xK χ ≫ (ι[D₂.P.A]).left := by
    show (toUnit _ ≫ D₂.c (-χ)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  choose J₁ hJ₀ using fun φ : (TK R₂).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (φ z)
  have hJ₁ : Good D₁.P.L z J₁ := hJ₀
  have vψ : ∀ a, val (D₁.psi (xe a)) (spMap gam) z J₁ =
      (gw v (D₂.xK a) z (J₁ (D₂.xK a ≫ β)) (J₂ (D₂.xK a)))⁻¹ * val (D₂.psi a) (𝟙 _) z J₂ := fun a => by
    have := GlobalTheory.CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ₁ hJ₂
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have hcorr := corr_of_val D₁.P.isLB (t := LB.mulGen _ _ _ _ _ (D₁.psi (-(xe χ))) (LB.pullGen _ _ _ D₁.sym (D₁.xK (xe χ))))
    (t' := GlobalTheory.UU.scaleGen (unitOn (h (xe χ))) (D₁.psi (xe χ))) fun y J hJ => by
      rw [val_mul hJ, val_pull hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, Category.id_comp]
      exact hE (xe χ) y J hJ
  have e := val_corr hJ₁ hcorr (spMap gam)
  have hg : gm (spMap gam) z ⊤ (unitOn (h (xe χ))) =
      gm (𝟙 (TK R₂).left) z ⊤ (unitOn (Units.map gam.toMonoidHom (h (xe χ)))) := gm_spMap_unitOn gam _ z
  rw [val_mul hJ₁, val_pull hJ₁, GlobalTheory.UU.val_scaleGen _ _ _ hJ₁, hg, ← cx, ← map_neg xe χ, vψ, vψ] at e
  have hs := GlobalTheory.PsiRing.val_sym_comp GlobalTheory.globalFns_holds gp hv (D₂.xK χ) z hJ₁ hJ₂
  rw [← cn] at hs
  rw [hs] at e
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PolDeg
