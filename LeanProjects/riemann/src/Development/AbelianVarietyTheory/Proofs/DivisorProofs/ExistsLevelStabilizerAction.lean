import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def nu (g : LevelAut Dw l) : SABMap Xo.univ.t Xo.univ.t (GlobalTheory.CompLevelStab.mv hpq hA Xo g) :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose

theorem nu_spec (g : LevelAut Dw l) :
    IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g) (nu hpq hA Xo g) (liftLa g) LinearMap.id :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.2

theorem nu_mul (c : Coeff l) (g h : LevelAut Dw l) : (nu hpq hA Xo (g * h)).φ = (nu hpq hA Xo g).φ ≫ (nu hpq hA Xo h).φ := by
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ (nu hpq hA Xo g) (nu hpq hA Xo h)
  have hg := nu_spec hpq hA Xo g
  have hh := nu_spec hpq hA Xo h
  have hc : IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g ≫ GlobalTheory.CompLevelStab.mv hpq hA Xo h) μ (liftLa (g * h))
      LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, hh.1, hg.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub g h a), hμ, ← Category.assoc, hg.2.1,
        Category.assoc, hh.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
          (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, hg.2.2, Category.assoc, hh.2.2, Category.assoc]
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.1
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo h).choose_spec.1
  rw [← hμ]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (g * h) (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo (g * h)).choose_spec.1
    inferInstance (nu_spec hpq hA Xo (g * h)) hc).2

end Moves

section Lift

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem j₀_ι' : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = i₀ TF.Y Z ≫ (TF.Y.jQ ≫ pullback.fst _ _) := j₀_ι TF.Y Z

def toF : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ TF.Y.oF.t.G.left :=
  TF.Y.m.cart.1.lift (pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z) (by
      rw [pullback.condition, Category.assoc]; exact congrArg (_ ≫ ·) (j₀_ι' TF Z))

theorem toF_m : toF TF Z ≫ TF.Y.m.φ = pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) :=
  TF.Y.m.cart.1.lift_fst _ _ _

theorem toF_hom : toF TF Z ≫ TF.Y.oF.t.G.hom =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z :=
  TF.Y.m.cart.1.lift_snd _ _ _

theorem toF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) TF.Y.oF.t.G (i₀ TF.Y Z) (toF TF Z) :=
  IsGrpPullback.cancel TF.Y.m.cart
    ((GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr (j₀_ι' TF Z) (toF_m TF Z).symm) (toF_hom TF Z)

def toU : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ Xo.univ.t.G.left := toF TF Z ≫ TF.Y.m0.toSABMap.φ

theorem toU_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) Xo.univ.t.G (i₀ TF.Y Z ≫ pullback.fst _ _)
    (toU TF Z) :=
  (toF_cart TF Z).comp TF.Y.m0.cart

theorem hom_ext' {T : Scheme.{0}} {u u' : T ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left}
    (h₁ : u ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
      u' ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (h₂ : u ≫ toU TF Z = u' ≫ toU TF Z) : u = u' :=
  (toU_cart TF Z).1.hom_ext h₂ h₁

end Lift

section Move

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem nF_w (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (toU TF Z ≫ (nu hpq hA Xo g).φ) ≫ Xo.univ.t.G.hom =
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) ≫ pullback.fst _ _ := by
  rw [Category.assoc, (nu hpq hA Xo g).cart.1.w, ← Category.assoc, (toU_cart TF Z).1.w, hr,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_fst]
  rfl

def nF (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left :=
  pullback.lift
    (TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) ≫ TF.Y.m.φ)
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r) (by
      rw [Category.assoc, TF.Y.m.cart.1.w, ← Category.assoc, TF.Y.m0.cart.1.lift_snd]
      simp only [Category.assoc]
      exact congrArg (fun x => _ ≫ r ≫ x) (j₀_ι' TF Z).symm)

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem nF_snd : nF hpq hA TF Z g r hr ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r :=
  pullback.lift_snd _ _ _

theorem nF_toF : nF hpq hA TF Z g r hr ≫ toF TF Z = TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, toF_hom, ← Category.assoc, nF_snd, Category.assoc, TF.Y.m0.cart.1.lift_snd]

theorem nF_toU : nF hpq hA TF Z g r hr ≫ toU TF Z = toU TF Z ≫ (nu hpq hA Xo g).φ := by
  rw [toU, ← Category.assoc, nF_toF]
  exact TF.Y.m0.cart.1.lift_fst _ _ _

theorem nF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) r
    (nF hpq hA TF Z g r hr) := by
  refine IsGrpPullback.cancel (toU_cart TF Z) (((toU_cart TF Z).comp (nu hpq hA Xo g).cart).congr ?_ ?_) ?_
  · rw [Category.assoc, ← GlobalTheory.CompLevelStab.mvF_fst, ← Category.assoc, ← hr, Category.assoc]
  · exact (nF_toU hpq hA TF Z g r hr).symm
  · exact nF_snd hpq hA TF Z g r hr

end Move

section Laws

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem act_toF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toF TF Z =
    toF TF Z ≫ (TF.Y.oF.t.act.act a).left := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m, Category.assoc, TF.Y.m.act a, ← Category.assoc, toF_m]
    exact GlobalTheory.EqvAct.pullAct_pullψ TF Z (j₀ TF.Y Z) a
  · rw [Category.assoc, toF_hom, Category.assoc, Over.w (TF.Y.oF.t.act.act a), toF_hom, ← Category.assoc]
    exact congrArg (· ≫ i₀ TF.Y Z) (Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a))

theorem act_toU (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toU TF Z =
    toU TF Z ≫ (Xo.univ.t.act.act a).left := by
  rw [toU, ← Category.assoc, act_toF, Category.assoc, TF.Y.m0.toSABMap.act a, Category.assoc]

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem act_nF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr =
    nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left := by
  apply hom_ext' TF Z
  · rw [Category.assoc, nF_snd, Category.assoc]
    have e := Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a)
    erw [e, ← Category.assoc, e]
    exact (nF_snd hpq hA TF Z g r hr).symm
  · have e1 : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr ≫ toU TF Z =
        toU TF Z ≫ (Xo.univ.t.act.act a).left ≫ (nu hpq hA Xo g).φ := by
      rw [nF_toU, ← Category.assoc, act_toU, Category.assoc]
    have e2 : (nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left) ≫ toU TF Z =
        toU TF Z ≫ (nu hpq hA Xo g).φ ≫ (Xo.univ.t.act.act a).left := by
      rw [Category.assoc, act_toU, ← Category.assoc, nF_toU, Category.assoc]
    rw [Category.assoc, e1, e2, (nu hpq hA Xo g).act a]

theorem sec_toU (b : Dw.La) (w : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left)
    (hw : w ≫ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _)
    (hb : w ≫ GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z) = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) :
    w ≫ toU TF Z = i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left := by
  have hF : w ≫ toF TF Z = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left := by
    apply TF.Y.m.cart.1.hom_ext
    · rw [Category.assoc, toF_m, Category.assoc]
      exact hb
    · rw [Category.assoc, toF_hom, ← Category.assoc]
      erw [hw]
      rw [Category.id_comp, Category.assoc, Over.w (TF.Y.oF.eta b)]
      exact (Category.comp_id _).symm
  rw [toU, ← Category.assoc, hF, Category.assoc, TF.Y.m0.eta b]

end Laws

theorem eqvAct_interior : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  intro _ E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ
  refine ⟨fun γ => nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).hom (hρ γ),
    ⟨fun γ => nF_cart hpq hA TF Z _ _ (hρ γ), fun γ a => act_nF hpq hA TF Z _ _ (hρ γ) a, fun γ₁ γ₂ => ?_⟩,
    fun γ a b hab w w' hw hw' hb ha => ?_⟩
  · apply hom_ext' TF Z
    · rw [nF_snd, Category.assoc, nF_snd, ← Category.assoc, nF_snd, Category.assoc, map_mul, Aut.Aut_mul_def]
      rfl
    · rw [nF_toU, Category.assoc, nF_toU, ← Category.assoc, nF_toU, Category.assoc, ← nu_mul hpq hA Xo c, map_mul,
        mul_inv_rev]
  · apply hom_ext' TF Z
    · rw [Category.assoc, nF_snd, ← Category.assoc, Category.assoc (ρ γ).hom]
      erw [hw, hw']
      rw [Category.id_comp, Category.comp_id]
    · have hq : b - liftLa (ι γ)⁻¹ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq]
        exact hab.trans (liftLa_spec (ι γ)⁻¹ a).symm
      have L : (w ≫ nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).hom (hρ γ)) ≫ toU TF Z =
          i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left ≫ (nu hpq hA Xo (ι γ)⁻¹).φ := by
        rw [Category.assoc, nF_toU, ← Category.assoc, sec_toU TF Z b w hw hb, Category.assoc, Category.assoc]
      have R : ((ρ γ).hom ≫ w') ≫ toU TF Z = (ρ γ).hom ≫ i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta a).left := by
        rw [Category.assoc, sec_toU TF Z a w' hw' ha]
      rw [L, R, GlobalTheory.LevelActionLaws.eta_congr Xo hq, (nu_spec hpq hA Xo (ι γ)⁻¹).2.1 a,
        ← Category.assoc (pullback.fst _ _), ← GlobalTheory.CompLevelStab.mvF_fst]
      simp only [← Category.assoc]
      rw [← hρ γ]

end GlobalTheory.EqvInterior
