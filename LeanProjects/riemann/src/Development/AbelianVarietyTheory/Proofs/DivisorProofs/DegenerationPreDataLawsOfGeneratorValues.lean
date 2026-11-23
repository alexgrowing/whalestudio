import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

namespace GenTr

theorem stalkMap_gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (q : Z ⟶ Y) (hq : r ≫ g = q) (z : Z)
    (J : (Z ⟶ X) → L.ι) :
    val t q z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) := by
  subst hq
  rw [val_of t g (r z) _ (fun k => J ((r ≫ g) ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (stalkMap_gm_comp r g z _ _).symm

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem val_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

end GenTr

open GenTr

theorem rlaws_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  intro R _ _ D₀ O _ _ _ onB hc w0 uw huw hnw ψ hR
  obtain ⟨hgen, h1, h2, h3, h4⟩ := hR
  have hL := D₀.P.isLB
  have htu := toUnit_TK_left R
  let Dn : DegPre R := { D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _ }
  have Fψ : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ y,
      val (Dn.psi y) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val (ψ y) (𝟙 _) ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ y => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp) _ _)
  have Frig : ∀ (z : (TK R).left) J, Good D₀.P.L z J →
      val Dn.rigK (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (rigV D₀ ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp [htu]) _ _)
  have Ftau : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a b : D₀.X,
      val (Dn.tau a b) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (tauV D₀ ψ ((jK R) z) (fun f => J (jK R ≫ f)) a b) := by
    intro z J hJ a b
    rw [val_tau Dn hJ, Fψ z J hJ, Fψ z J hJ, Fψ z J hJ, Frig z J hJ, tauV, map_mul, map_mul, map_mul, map_inv, map_inv,
      map_inv]
    rfl
  have Fx : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K] (φ : K → (D₀.P.A.left ⟶ D₀.P.A.left))
      (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.xK y)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val t (D₀.c y).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp]
    show _ = (toUnit (TK R) ≫ D₀.c y).left
    rw [Over.comp_left, htu]
  have F2 : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K]
      (φ : K → ((D₀.P.A ⊗ D₀.P.A).left ⟶ D₀.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y y' : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.pt2 y y')) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val t (lift (D₀.c y) (D₀.c y')).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y y'
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt2, ← htu, ← Over.comp_left, comp_lift]
  have Fcub : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a a' b : D₀.X,
      val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val D₀.cub.t (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ a a' b
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt3, ← htu, ← Over.comp_left, comp_lift, comp_lift]
  refine ⟨fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _, ⟨onB, hc, ?_⟩, rfl, ?_, ?_, ⟨uw, huw, hnw, ?_⟩, ?_⟩
  · intro a u hu hun y y'
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Ftau z J hJ, F2 z J hJ, Ftau z J hJ, ← map_mul]
    exact congrArg _ (h3 a u hu hun y y' _ _ fun f => hJ _)
  · intro χ
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Fψ z J hJ, Fx z J hJ, Fψ z J hJ, ← map_mul]
    exact congrArg _ (h2 χ _ _ fun f => hJ _)
  · intro a a' b
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau (a + a') b) (𝟙 _) z J *
        val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
          val (Dn.tau a b) (𝟙 _) z J * val (Dn.tau a' b) (𝟙 _) z J := by
      rw [Ftau z J hJ, Fcub z J hJ, Ftau z J hJ, Ftau z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h1 a a' b _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau y (w0 • y)) (𝟙 _) z J * val (LB.pullGen D₀.P.L _ _ uw (Dn.xK y)) (𝟙 _) z J =
        val (Dn.psi y) (𝟙 _) z J * val Dn.rigK (𝟙 _) z J := by
      rw [Ftau z J hJ, Fx z J hJ, Fψ z J hJ, Frig z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h4 y _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y j V _ _ hV h
    have hle : V ≤ LB.wchart D₀.P.L (fun _ : PUnit => (D₀.c y).left) j :=
      fun x hx => Set.mem_iInter.2 fun _ => hV hx
    refine ⟨(res hle ((ψ y).s j)).val, Units.isUnit _, ?_⟩
    have e := congrArg (fun q => q.hom ((ψ y).s j).val) ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.trans ?_
    show _ = ((TK R).left.presheaf.map (homOfLE h).op).hom (((TK R).left.presheaf.map (homOfLE _).op).hom
      (((jK R).app _).hom ((ψ y).s j).val))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.UTau0
