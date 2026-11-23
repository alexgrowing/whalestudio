import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorPull

section PFactorPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [GrpObj C]
  [GrpObj B₁] [GrpObj C₁] [IsCommMonObj C] [IsCommMonObj C₁] {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}

theorem lift_sq_of (β₂ : (G2 B₁).left ⟶ (G2 B).left) (hsq : IsSquare β β₂) (gC : IsGrpPullback C₁ C f δ)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ sqOf gC =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, (isSquare_sqOf gC).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hsq.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, (isSquare_sqOf gC).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hsq.2, Category.assoc]

end PFactorPull

set_option maxHeartbeats 800000 in

theorem pfactor_pull : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R R' _ _ _ _ ρ hρ Q D' F D ε hR D₁' hD' _ o₁ hx ho
  obtain ⟨β, β₂, wR, gB, hsq, hwR, hcR, htR⟩ := hR
  have gC := pull_grp hD'
  obtain ⟨inc, mi, hi⟩ := hom_pull gB gC F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gC gB F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : D.X →+ D₁'.X, ∀ y, hD'.xe (xi y) = F.xi (ε y) :=
    ⟨hD'.xe.symm.toAddMonoidHom.comp (F.xi.comp ε.toAddMonoidHom), fun y => hD'.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁'.X →+ D.X, ∀ y, ε (xp y) = F.xp (hD'.xe y) :=
    ⟨ε.symm.toAddMonoidHom.comp (F.xp.comp hD'.xe.toAddMonoidHom), fun y => ε.apply_symm_apply _⟩
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ proj hD' = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  have hm := lift_sq_of β₂ hsq gC hi hf
  obtain ⟨w, hw, vw⟩ := GlobalTheory.T.mumfordBundleIso_square_passes_second_iso gC Q.M.isLB D'.P.isLB D.P.isLB D₁'.P.isLB β₂ wR hwR hD'.w hD'.w_gen hm F.w F.w_gen
  have hc : ∀ y, D₁'.c (xi y) = D.c y ≫ inc := fun y => ext_pull gC (by
    rw [hD'.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (D.c y).left,
      hcR, Category.assoc])
  refine ⟨inc, pr, xi, xp, w, mi, mp, ext_pull gB ?_, ext_pull gC ?_, fun y => ε.injective ?_,
    fun y => hD'.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_, hw, fun a b z I₁ J₁ hI₁ hJ₁ => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD'.xe h
    simp only [hx, hxi] at h'
    exact ε.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD'.xe z)
    refine ⟨ε.symm y, hD'.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ε.apply_symm_apply, hy]
  · obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' Q.M.isLB z
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' D'.P.isLB z
    let g₀ := genMap hρ
    have sq : (TK R').hom ≫ spMap ρ = g₀ ≫ (TK R).hom := (Category.id_comp _).symm.trans (fracMap_sq hρ)
    have hκ : g₀ ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hρ).symm.trans (Category.id_comp _)
    have cQ : ∀ y, (toUnit (TK R') ≫ D.c y).left ≫ β = g₀ ≫ (toUnit (TK R) ≫ Q.c (ε y)).left := fun y => by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hcR, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (Q.c (ε y)).left) sq
    have hP : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫ β₂ =
        g₀ ≫ (lift (toUnit (TK R) ≫ Q.c (ε a)) (toUnit (TK R) ≫ Q.c (ε b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact cQ a
      · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact cQ b
    have hQ : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left =
        (lift (toUnit (TK R') ≫ D₁'.c (xi a)) (toUnit (TK R') ≫ D₁'.c (F.f • xi b))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hc, hc]
      simp only [Category.assoc]
    have R₁ := htR g₀ hκ a b z J J₁ hJ hJ₁
    have t₁ := F.tau (ε a) (ε b) (g₀ z) (fun ψ => I (g₀ ≫ ψ)) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => hI (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (Q.tau (ε a) (ε b)) (g₀ ≫ 𝟙 _) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (ε a) (ε b)) (𝟙 _) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J hJ).2.2.1 _)
    have n₂ : val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (g₀ ≫ 𝟙 _) z I =
        Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (𝟙 _) (g₀ z) (fun ψ => I (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z I hI).2.2.1 _)
    rw [Category.comp_id] at n₁ n₂
    have E := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp F.w g₀ _ z I J hI hJ).symm n₂.symm))
    have K := vw _ (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z I J I₁ J₁ hI hJ hI₁ hJ₁
    rw [hP, hQ] at K
    have a₂ := tau_lam hD' hρ (xi a) (F.f • xi b) hI hI₁
    rw [hx, hxi, hxi] at a₂
    rw [R₁, ← a₂, E, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (lamVal w _ z I₁ J₁), K,
      mul_comm (lamVal F.w _ z I J)]

end GlobalTheory.FactorPull

end
