import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBaseStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenBundle

variable {X Y Z : Scheme.{0}}

theorem lbIso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_comp' {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (chartPullSame L (fun _ : PUnit => g ≫ f) (fun _ => f) (fun _ => 1) g fun _ => rfl)
    (chartPullPull _ g) (lbIso_self (pull_isLB hL f))

end GlobalTheory.Mum.GenBundle

open GlobalTheory.Mum.GenBundle in

theorem GlobalTheory.Mum.genBundle_extends : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w := by
  intro R R' _ _ _ _ _ ρ hA _ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ h1 h2
  obtain ⟨hN, -, hI, -⟩ := hA
  haveI := D₃.P.isAb
  haveI : Smooth D₃.P.A.hom := D₃.P.isAb.smooth
  haveI : GeometricallyIntegral D₃.P.A.hom := geometricallyIntegral_of_isAbelianScheme D₃.P.A
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL₃ := D₃.P.isLB
  have hLE := E.P.isLB
  have a₁ : LBIso (D₃.P.L.pull κ) (D₁.P.L.pull (GlobalTheory.PsiEvenPull.proj q₁)) :=
    LBIso.chartPull (chartPullPull D₃.P.L κ)
      (chartPullSame D₁.P.L (fun _ : PUnit => GlobalTheory.PsiEvenPull.proj q₁) (fun _ => GlobalTheory.PsiEvenPull.proj p)
        (fun _ => 1) κ fun _ => h1.symm) ⟨p.w, p.w_gen⟩
  have a : LBIso (D₃.P.L.pull κ) E.P.L :=
    LBIso.trans (pull_isLB hL₃ κ) (pull_isLB hL₁ _) hLE a₁ (LBIso.symm ⟨q₁.w, q₁.w_gen⟩)
  have b₀ : LBIso E.P.L (D₂.P.L.pull (κ ≫ Φ)) := h2 ▸ ⟨q₂.w, q₂.w_gen⟩
  have b : LBIso (D₃.P.L.pull κ) ((D₂.P.L.pull Φ).pull κ) :=
    LBIso.trans (pull_isLB hL₃ κ) (pull_isLB hL₂ _) (pull_isLB (pull_isLB hL₂ Φ) κ)
      (LBIso.trans (pull_isLB hL₃ κ) hLE (pull_isLB hL₂ _) a b₀) (lbIso_pull_comp' hL₂ Φ κ)
  have hj : pullback.fst D₃.P.A.hom (jK R') = hκ.1.isoPullback.inv ≫ κ := by
    exact (Iso.inv_hom_id_assoc hκ.1.isoPullback _).symm.trans
      (congrArg (hκ.1.isoPullback.inv ≫ ·) hκ.1.isoPullback_hom_fst)
  have c : LBIso (D₃.P.L.pull (pullback.fst D₃.P.A.hom (jK R')))
      ((D₂.P.L.pull Φ).pull (pullback.fst D₃.P.A.hom (jK R'))) :=
    LBIso.chartPull
      (chartPullSame D₃.P.L (fun _ : PUnit => pullback.fst D₃.P.A.hom (jK R')) (fun _ => κ) (fun _ => 1)
        hκ.1.isoPullback.inv fun _ => hj)
      (chartPullSame (D₂.P.L.pull Φ) (fun _ : PUnit => pullback.fst D₃.P.A.hom (jK R')) (fun _ => κ) (fun _ => 1)
        hκ.1.isoPullback.inv fun _ => hj) b
  obtain ⟨w, hw⟩ := GlobalTheory.Mum.lbIso_of_generic_local R' D₃.P.A (eSec D₃.P.A) (Over.w η[D₃.P.A]) D₃.P.L
    (D₂.P.L.pull Φ) hL₃ (pull_isLB hL₂ Φ) c
  exact ⟨w, (isGen_iff w).1 hw⟩
