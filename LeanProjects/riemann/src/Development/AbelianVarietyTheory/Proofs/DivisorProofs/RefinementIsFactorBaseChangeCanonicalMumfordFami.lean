import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumBC

open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in
set_option maxHeartbeats 1600000 in

theorem refine_factor_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  intro R _ _ _ hCN Q G _ _ P hG hC R' _ _ _ ρ hCN' hρ hfin D ε hRef
  obtain ⟨hPL, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, mi, mp, hip, hpi, hP⟩ := hC
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hR' := admissibleBase_of_completeNormalLocalCharZero hCN'
  have hloc : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    have hint : Algebra.IsIntegral R R' := ⟨fun x => RingHom.IsIntegral.of_finite hfin x⟩
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal R')
    have hc : (maximalIdeal R').comap ρ = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal R').comap ρ := hc.symm ▸ (mem_maximalIdeal a).2 hna
    exact (mem_maximalIdeal _).1 this ha
  obtain ⟨D₁', hD', A₁', U₁', hU, oG₁, oA₁, h₁, h₂⟩ :=
    unif_pull hR hR' ρ hρ (map_maximalIdeal_le ρ) hG' U' F.O F.o oA oG hlin
  obtain ⟨m, o₁, hx, ho⟩ := degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R R' ρ _ _ hD' F.O F.o
  have lin := oLinear_pull R R' _ _ ρ D' D₁' hD' A' A₁' G' _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) U' U₁' hU
    F.O F.o o₁ oA oA₁ oG oG₁ hlin h₁ h₂ hx ho
  obtain ⟨inc', pr', xi, xp, w, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁⟩ :=
    GlobalTheory.T.polarisedIdempotentFactor_pullback_refinement ρ hρ Q D'.toPre F D.toPre ε hRef D₁'.toPre hD' o₁ hx fun a => act_proj _ hD'.e.hom (ho a)
  let F₁ : Factor D.toPre D₁'.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := b₁₀, tau := b₁₁ }
  have alg : F₁.Alg := F.alg
  have ha : ∀ a, oG₁.act a = (Over.pullback (specOf ρ)).map (oG.act a) := fun a =>
    (Category.comp_id _).symm.trans ((h₁ a).trans (Category.id_comp _))
  have gG := isGrpPullback_pullback G (specOf ρ)
  have gG' := (isGrpPullback_pullback G' (specOf ρ)).congr rfl (Category.id_comp _).symm
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁', F₁, alg, A₁', _, _, _, U₁', oA₁, oG₁, (Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Over.pullback (specOf ρ)).map inc, (Over.pullback (specOf ρ)).map pr, _, sqOf gG,
    IsSemiAbelian.pullback _ G' hG', lin, IsSemiAbelian.pullback _ G hG, inferInstance, inferInstance, ?_, ?_, gG,
    isSquare_sqOf gG, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, hpi, ha]
  · have hm := lift_sq gG gG' (u := inc) (v := inc ≫ oG.act F.f) (u₁ := (Over.pullback (specOf ρ)).map inc)
      (v₁ := (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f)
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (map_left_fst _ _))
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (by
        rw [ha, ← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _))
    have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
    have H1 : LBIso ((abelian₂ ((Over.pullback (specOf ρ)).obj G') U₁'.LG.L).pull
        (lift (fst _ _ ≫ (Over.pullback (specOf ρ)).map inc) (snd _ _ ≫ (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f) :
          G2 ((Over.pullback (specOf ρ)).obj G) ⟶ G2 ((Over.pullback (specOf ρ)).obj G')).left)
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb (abelian₂ G' U'.LG.L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
    have H2 : LBIso (P.pull (sqOf gG))
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      hP.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl)
    exact LBIso.trans (pull_isLB (DVR.linComb_isLB _ U₁'.LG.isLB _ _) _)
      (pull_isLB (pull_isLB (DVR.linComb_isLB _ U'.LG.isLB _ _) _) _) (pull_isLB hPL _) H1 (LBIso.symm H2)

end GlobalTheory.MumBC

end
