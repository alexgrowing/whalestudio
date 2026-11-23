import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PreLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

private lemma app_res_app_res_lemma {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (O : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hO : O ≤ f ⁻¹ᵁ V) (hO' : O ≤ (f ≫ g) ⁻¹ᵁ U) :
    g.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ f.app V ≫ X.presheaf.map (homOfLE hO).op =
      (f ≫ g).app U ≫ X.presheaf.map (homOfLE hO').op := by
  first
    | rw [Scheme.Hom.naturality_assoc]
    | rw [← Scheme.Hom.naturality_assoc]
  rw [← Functor.map_comp, ← Category.assoc]
  rfl

private lemma res_app_res_lemma_2 {X Y : Scheme.{0}} (f : X ⟶ Y) (V₁ V : Y.Opens) (O : X.Opens)
    (hV : V₁ ≤ V) (hO : O ≤ f ⁻¹ᵁ V₁) (hO' : O ≤ f ⁻¹ᵁ V) :
    Y.presheaf.map (homOfLE hV).op ≫ f.app V₁ ≫ X.presheaf.map (homOfLE hO).op =
      f.app V ≫ X.presheaf.map (homOfLE hO').op := by
  first
    | rw [Scheme.Hom.naturality_assoc]
    | rw [← Scheme.Hom.naturality_assoc]
  rw [← Functor.map_comp]
  rfl

theorem unit_norm_pull {S₁ S₂ Y Z : Scheme.{0}} (e₁ : S₁ ⟶ Y) (e₂ : S₂ ⟶ Z) (a : Z ⟶ Y) (ff : S₂ ⟶ S₁)
    (he : e₂ ≫ a = ff ≫ e₁) {W : Y.Opens} (u : Γ(Y, W)ˣ) {W' : Z.Opens} (hW' : W' ≤ a ⁻¹ᵁ W)
    {V : S₁.Opens} (r : Γ(S₁, V)ˣ) {V' : S₂.Opens} (hV' : V' ≤ ff ⁻¹ᵁ V)
    (h : res (inf_le_left : e₁ ⁻¹ᵁ W ⊓ V ≤ e₁ ⁻¹ᵁ W) (pullU e₁ W u) *
      res (inf_le_right : e₁ ⁻¹ᵁ W ⊓ V ≤ V) r = 1) :
    res (inf_le_left : e₂ ⁻¹ᵁ W' ⊓ V' ≤ e₂ ⁻¹ᵁ W') (pullU e₂ W' (res hW' (pullU a W u))) *
      res (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V') (res hV' (pullU ff V r)) = 1 := by
  have p1 : e₂ ⁻¹ᵁ W' ⊓ V' ≤ (e₂ ≫ a) ⁻¹ᵁ W :=
    inf_le_left.trans ((TopologicalSpace.Opens.map e₂.base).map (homOfLE hW')).le
  have p2 : e₂ ⁻¹ᵁ W' ⊓ V' ≤ (ff ≫ e₁) ⁻¹ᵁ W := by rw [← he]; exact p1
  have hq : e₂ ⁻¹ᵁ W' ⊓ V' ≤ ff ⁻¹ᵁ V :=
    inf_le_right.trans hV'
  have hO : e₂ ⁻¹ᵁ W' ⊓ V' ≤ ff ⁻¹ᵁ (e₁ ⁻¹ᵁ W ⊓ V) := by
    show _ ≤ ff ⁻¹ᵁ (e₁ ⁻¹ᵁ W) ⊓ ff ⁻¹ᵁ V
    exact le_inf p2 hq
  have hC : ∀ (g₁ g₂ : S₂ ⟶ Y) (_ : g₁ = g₂) (p : e₂ ⁻¹ᵁ W' ⊓ V' ≤ g₁ ⁻¹ᵁ W)
      (q : e₂ ⁻¹ᵁ W' ⊓ V' ≤ g₂ ⁻¹ᵁ W),
      g₁.app W ≫ S₂.presheaf.map (homOfLE p).op = g₂.app W ≫ S₂.presheaf.map (homOfLE q).op := by
    intro g₁ g₂ hg p q
    subst hg
    rfl
  have hA := app_res_app_res_lemma e₂ a W W' (e₂ ⁻¹ᵁ W' ⊓ V') hW' inf_le_left p1
  have hB := app_res_app_res_lemma ff e₁ W (e₁ ⁻¹ᵁ W ⊓ V) (e₂ ⁻¹ᵁ W' ⊓ V') inf_le_left hO p2
  have hAB := hA.trans ((hC _ _ he p1 p2).trans hB.symm)
  have hD := res_app_res_lemma_2 ff (e₁ ⁻¹ᵁ W ⊓ V) V (e₂ ⁻¹ᵁ W' ⊓ V') inf_le_right hO hq
  have hE : ff.app V ≫ S₂.presheaf.map (homOfLE hV').op ≫
      S₂.presheaf.map (homOfLE (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V')).op =
      ff.app V ≫ S₂.presheaf.map (homOfLE hq).op := by
    rw [← Functor.map_comp]
    rfl
  have key := congrArg (fun t => res hO (pullU ff _ t)) h
  simp only [map_mul, map_one] at key
  refine Eq.trans ?_ key
  congr 1
  · ext
    have hu := congrArg (fun φ => φ.hom (u : Γ(Y, W))) hAB
    simpa [res, pullU] using hu
  · ext
    have hr := congrArg (fun φ => φ.hom (r : Γ(S₁, V))) (hE.trans hD.symm)
    simpa [res, pullU] using hr

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

attribute [local instance] SplitExt.free SplitExt.finite

variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

theorem unit_normB (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X) :
    res (inf_le_left : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j))
        (pullU (eSec ((Over.pullback f).obj G)) _ (uB f E d j k)) *
      res (inf_le_right : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k))
        (((pullExt f E).O ((pullExt f E).basis k)).rig.s (fun _ => j k)) = 1 := by
  have hmB : (mB f E).e = f := rfl
  have he : eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f = (mB f E).e ≫ eSec G := by
    rw [hmB]
    simp [eSec]
    refine (pullback.lift_fst _ _ _).trans ?_
    simpa using (pullback.condition_assoc (f := 𝟙 S) (g := f) η[G].left)
  exact unit_norm_pull (eSec G) (eSec ((Over.pullback f).obj G)) (pullback.fst G.hom f) (mB f E).e he
    (d.u (jj f E j) k) (pre_le f E d j) ((E.O (E.basis k)).rig.s (fun _ => jj f E j k))
    (rigPull_le (mB f E).F (mB f E).e (mB f E).e_comm (E.O (E.basis k)).L (fun _ => j k))
    (d.unit_norm (jj f E j) k)

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
