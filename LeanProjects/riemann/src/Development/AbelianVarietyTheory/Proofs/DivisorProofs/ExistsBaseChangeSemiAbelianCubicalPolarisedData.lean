import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_baseChange_semiAbelian_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  intro R _ _ _ _ G _ _ hG P A gen hmon hext R' _ _ _ ρ _ hfin
  have hinj : Function.Injective ρ := hfin.2.1

  have gpG₁ : IsGrpPullback ((Over.pullback (spMap ρ)).obj G) G (spMap ρ) (pullback.fst G.hom (spMap ρ)) :=
    isGrpPullback_pullback G (spMap ρ)
  obtain ⟨β₂, hsq, hlam⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ) G ((Over.pullback (spMap ρ)).obj G) _ gpG₁

  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap (hw := pullback.condition) P
    (GlobalTheory.UU.toBase_mul_pullback G (spMap ρ)) _ (pull_isLB P.L.isLB _) _ (GlobalTheory.UU.pullIso_isGen P.L.isLB _)
  let P₁ : GlobalTheory.UU.CP ((Over.pullback (spMap ρ)).obj G) :=
    ⟨⟨P.L.L.pull (pullback.fst G.hom (spMap ρ)), rig, pull_isLB P.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩

  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  haveI := hmon
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have gpGen : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ :=
    (GlobalTheory.ArcPull.fracMap_sq hinj).symm.trans (Category.id_comp _)
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G
      (spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp gpG₁).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpGen)
  refine ⟨(Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance, pullback.fst G.hom (spMap ρ), β₂, P₁, A', eA,
    IsSemiAbelian.pullback _ G hG, gpG₁, hsq, mE, ?_, ?_⟩
  · refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb P.L.L (pullback.fst G.hom (spMap ρ))
        (fun _ => pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R'))
        (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  · have hL := P.L.isLB
    have h := hlam P.L.L (P.L.L.pull (pullback.fst G.hom (spMap ρ))) _ (abelian₂ G P.L.L) (𝟙 _) hL (pull_isLB hL _)
      (LB.isLB_linComb hL _ _) (lbIso_refl (pull_isLB hL _)) (LBIso.symm (lbIso_pull_id (LB.isLB_linComb hL _ _)))
    rwa [Category.comp_id] at h

end GlobalTheory.Mum
