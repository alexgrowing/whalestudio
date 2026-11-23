import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.PFactorPull

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.FactorPull in

theorem algebraic_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X) (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B (spMap θ) β → (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) → ∃ (inc : Q'.B ⟶ D₁.P.A) (pr : D₁.P.A ⟶ Q'.B) (xi : Q'.X →+ D₁.X) (xp : D₁.X →+ Q'.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left ∧ (∀ y, hD.xe (xi y) = F.xi (ex y)) ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) ∧ (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁.X, ∃ y, star F.e • z = star F.e • F.f • xi y) := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex β gp hcβ
  have gp' := pull_grp hD
  obtain ⟨inc, mi, hi⟩ := hom_pull gp gp' F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gp' gp F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : Q'.X →+ D₁.X, ∀ y, hD.xe (xi y) = F.xi (ex y) :=
    ⟨hD.xe.symm.toAddMonoidHom.comp (F.xi.comp ex.toAddMonoidHom), fun y => hD.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁.X →+ Q'.X, ∀ y, ex (xp y) = F.xp (hD.xe y) :=
    ⟨ex.symm.toAddMonoidHom.comp (F.xp.comp hD.xe.toAddMonoidHom), fun y => ex.apply_symm_apply _⟩
  have hc : ∀ y, D₁.c (xi y) = Q'.c y ≫ inc := fun y => ext_pull gp' (by
    rw [hD.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (Q'.c y).left,
      hcβ, Category.assoc]
    try rfl)
  refine ⟨inc, pr, xi, xp, hi, hxi, mi, mp, ext_pull gp ?_, ext_pull gp' ?_, fun y => ex.injective ?_,
    fun y => hD.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD.xe h
    simp only [hx, hxi] at h'
    exact ex.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD.xe z)
    refine ⟨ex.symm y, hD.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ex.apply_symm_apply, hy]

end GlobalTheory.PFactorPull
