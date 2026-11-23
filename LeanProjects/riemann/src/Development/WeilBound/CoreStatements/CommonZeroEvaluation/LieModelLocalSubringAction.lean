import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsCorr
open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace ModelDimension.Tan

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem tanY_base {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [Algebra S T]
    [IsScalarTower c.F S T] (y : FrPt Xo c S) (z : FrPt Xo c T) (hx : z.x = spMap (algebraMap S T) ≫ y.x)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (hu : z.u τ i = spMap (Formalism.L2.Pj.dualMap (algebraMap S T)) ≫ y.u τ i) :
    Small.tanY Y z τ i = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap S T)) ≫ Small.tanY Y y τ i := by
  have hF : Small.ptF z = spMap (algebraMap S T) ≫ Small.ptF y := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Small.ptF_fst, Small.ptF_fst, hx]
    · rw [Category.assoc, Small.ptF_snd, Small.ptF_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
  rw [Small.tanY, Small.tanY, ← Category.assoc,
    Small.eq_tanF Y z τ i (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap S T)) ≫ Small.tanF Y y τ i)]
  · rw [Category.assoc, Small.tanF_φ, hu]
    rfl
  · rw [Category.assoc, Small.tanF_hom, hF, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_basis {X : Scheme.{0}} (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) {S : Type} [CommRing S]
    [Algebra c.F S] (z : Spec (CommRingCat.of S) ⟶ X) (y : FrPt Xo c S) (hy : Small.ptY Y y = z ≫ f) (τ : E →+* ℂ) :
    ∃ ub : Fin (Dw.mult τ) → (GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ tX.G), (∀ i, (ub i).left ≫ m.φ = Small.tanY Y y τ i) ∧
      (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G z (ub i)) ∧
      (∀ i a, ub i ≫ tX.act.act a = sc z (algebraMap c.F S (embK c τ a)) ≫ ub i) ∧
      ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G z v →
        (∀ a, v ≫ tX.act.act a = sc z (algebraMap c.F S (embK c τ a)) ≫ v) →
        ∃ cf : Fin (Dw.mult τ) → S, v = (List.ofFn fun i => sc z (cf i) ≫ ub i).prod := by
  obtain ⟨C1, h1⟩ := exists_corr (a₁ := tX.act.act) (a₂ := Y.t.act.act) m.cart m.act hy.symm
  obtain ⟨C2, h2⟩ := exists_corr (a₁ := Y.oF.t.act.act) (a₂ := Y.t.act.act) (x₁ := Small.ptF y)
    (x₂ := Small.ptY Y y) Y.m.cart Y.m.act rfl
  obtain ⟨C3, h3⟩ := exists_corr (a₁ := Y.oF.t.act.act) (a₂ := Xo.univ.t.act.act) Y.m0.cart Y.m0.act
    (Small.ptF_fst y)
  let Θ := (C3.symm.trans C2).trans C1.symm
  let u : Fin (Dw.mult τ) → (GlobalTheory.CompanionTheory.Ar.epsAt y.x ⟶ Xo.univ.t.G) := fun i =>
    CategoryTheory.Over.homMk (y.u τ i) (y.tan τ i).1
  refine ⟨fun i => Θ.e (u i), fun i => ?_, fun i => (Θ.tan _).2 (y.tan τ i).2, fun i a => ?_, fun v hv hE => ?_⟩
  · have e1 : C1.e (Θ.e (u i)) = C2.e (C3.e.symm (u i)) := C1.e.apply_symm_apply _
    have e2 : (C3.e.symm (u i)).left = Small.tanF Y y τ i := by
      refine Small.eq_tanF Y y τ i _ ?_ (CategoryTheory.Over.w _)
      exact (h3 _).symm.trans (congrArg (fun q => q.left) (C3.e.apply_symm_apply (u i)))
    refine (h1 _).symm.trans ?_
    rw [e1, h2, e2]
    rfl
  · rw [← Θ.act, ← Θ.scale]
    exact congrArg Θ.e (CategoryTheory.Over.OverMorphism.ext (y.eig τ i a))
  · obtain ⟨p, rfl⟩ := Θ.e.surjective v
    have hp : Formalism.L2.Pj.IsTanAt y.x p.left := ⟨CategoryTheory.Over.w p, (Θ.tan p).1 hv⟩
    have hpE : Formalism.L2.Pj.IsEigAt c τ (Xo := Xo) p.left := fun a => by
      have e := hE a
      rw [← Θ.act, ← Θ.scale] at e
      exact congrArg (fun q => q.left) (Θ.e.injective e)
    obtain ⟨cf, ⟨U, hU, hp'⟩, -⟩ := y.basis τ _ hp hpE
    have e1 : p = (List.ofFn U).prod := CategoryTheory.Over.OverMorphism.ext hp'.symm
    refine ⟨cf, ?_⟩
    rw [e1, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    refine Eq.trans ?_ (Θ.scale (cf i) (u i))
    exact congrArg Θ.e (CategoryTheory.Over.OverMorphism.ext (hU i))

end ModelDimension.Tan

theorem ModelDimension.lie_model_local_subring_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (Ω : Type) [Field Ω] [Algebra c.F Ω] (A : Subring Ω) [IsLocalRing A] [Algebra c.F A] [IsScalarTower c.F A Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel tX.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li), M.IsActOf tX.act.act ρ → ∀ (zq : Spec (CommRingCat.of A) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq = ξ → ∀ (y : FrPt Xo c A), Small.ptY Y y = zq ≫ f → ∀ yΩ : FrPt Xo c Ω, yΩ.x = spMap (algebraMap A Ω) ≫ y.x → (∀ τ i, yΩ.u τ i = spMap (Formalism.L2.Pj.dualMap (algebraMap A Ω)) ≫ y.u τ i) → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ), ∃ w : Fin r → Li, (∀ i, (M.pt (w i)).left ≫ m.φ = Small.tanY Y yΩ τ (Fin.cast hr i)) ∧ ∀ e : Li, ((∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zq ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zq v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ v.left) ∧ e ∈ eigSp ρ ((algebraMap c.F Ω).comp (embK c τ))) ↔ e ∈ Submodule.span A (Set.range w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m Ω _ _ A _ _ _ ξ _ Li _ _ M ρ hρ zq hz y hy yΩ hx hu τ r hr
  subst hr
  obtain ⟨ub, hb1, hb2, hb3, hb4⟩ := ModelDimension.Tan.exists_basis Y tX f m zq y hy τ
  obtain ⟨w, hw1, hw2⟩ := ModelDimension.Tan.span_eig (R := A) (F := Ω) Subtype.val_injective zq ξ hz M tX.act.act tX.act.hom ρ hρ
    ((algebraMap c.F A).comp (embK c τ)) ((algebraMap c.F Ω).comp (embK c τ))
    (fun a => IsScalarTower.algebraMap_apply c.F A Ω _) ub hb2 hb3 hb4
  refine ⟨w, fun i => ?_, hw2⟩
  rw [hw1, Category.assoc, hb1]
  exact (ModelDimension.Tan.tanY_base Y y yΩ hx τ i (hu τ i)).symm
