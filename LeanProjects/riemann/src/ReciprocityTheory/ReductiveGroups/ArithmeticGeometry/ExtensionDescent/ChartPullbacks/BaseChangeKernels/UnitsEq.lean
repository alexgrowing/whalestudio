import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PreLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

section General

theorem gmRP {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U)
    (hz : z ∈ V) (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u :=
  (gm_res (𝟙 Z) z hle hz _).trans ((gm_pull (𝟙 Z) a z U (hle hz) u).trans (by rw [Category.id_comp]))

theorem act_le_of_hom {S : Scheme.{0}} {B G T : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
    [IsMonHom q] (i : T ⟶ G) (hk : i ≫ q = toUnit _ ≫ η[B]) (U : B.left.Opens) :
    (snd T G).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) ≤
      (lift (fst T G ≫ i) (snd T G) ≫ μ[G]).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
  have e : (lift (fst T G ≫ i) (snd T G) ≫ μ[G]) ≫ q = snd T G ≫ q := by
    rw [← Hom.mul_def, MonObj.mul_comp, Category.assoc, hk, ← Hom.one_def, MonObj.comp_one,
      _root_.one_mul]
  have e' : (lift (fst T G ≫ i) (snd T G) ≫ μ[G]).left ≫ q.left = (snd T G).left ≫ q.left := by
    rw [← Over.comp_left, e, Over.comp_left]
  intro y hy
  have e₁ := congrArg (fun g => g y) e'
  simp only [Scheme.Hom.comp_apply] at e₁
  exact (congrArg (· ∈ U) e₁).mpr hy

theorem equivPullL {T₁ T₂ Y Z P₁ P₂ : Scheme.{0}} (act₁ s₁ : P₁ ⟶ Y) (f₁ : P₁ ⟶ T₁)
    (act₂ s₂ : P₂ ⟶ Z) (f₂ : P₂ ⟶ T₂) (b : P₂ ⟶ P₁) (a : Z ⟶ Y) (h : T₂ ⟶ T₁)
    (W : Y.Opens) (u : Γ(Y, W)ˣ) (W' : Z.Opens) (hW' : W' ≤ a ⁻¹ᵁ W)
    (c : Γ(T₁, ⊤)ˣ) (c' : Γ(T₂, ⊤)ˣ)
    (hc : res (fun _ _ => trivial : (⊤ : T₂.Opens) ≤ h ⁻¹ᵁ ⊤) (pullU h ⊤ c) = c')
    (le₁ : s₁ ⁻¹ᵁ W ≤ act₁ ⁻¹ᵁ W) (t₁ : s₁ ⁻¹ᵁ W ≤ f₁ ⁻¹ᵁ ⊤)
    (H : res le₁ (pullU act₁ W u) = res t₁ (pullU f₁ ⊤ c) * pullU s₁ W u)
    (ha : act₂ ≫ a = b ≫ act₁) (hs : s₂ ≫ a = b ≫ s₁) (hf : f₂ ≫ h = b ≫ f₁)
    (le₂ : s₂ ⁻¹ᵁ W' ≤ act₂ ⁻¹ᵁ W') (t₂ : s₂ ⁻¹ᵁ W' ≤ f₂ ⁻¹ᵁ ⊤) :
    res le₂ (pullU act₂ W' (res hW' (pullU a W u))) =
      res t₂ (pullU f₂ ⊤ c') * pullU s₂ W' (res hW' (pullU a W u)) := by
  refine unit_ext fun y hy => ?_
  have hsy : s₂ y ∈ W' := hy
  have hby : b y ∈ s₁ ⁻¹ᵁ W := by
    have e₁ := congrArg (fun g => g y) hs
    simp only [Scheme.Hom.comp_apply] at e₁
    show s₁ (b y) ∈ W
    rw [← e₁]
    exact hW' hsy
  have hay : act₂ y ∈ W' := le₂ hy
  have o := congrArg (gm b y (s₁ ⁻¹ᵁ W)) H
  rw [map_mul, gm_res b y _ hby, gm_res b y _ hby, gm_pull b act₁ y W (le₁ hby),
    gm_pull b f₁ y ⊤ trivial, gm_pull b s₁ y W hby, ← ha, ← hs, ← hf] at o
  have e3 : gm f₂ y ⊤ c' = gm (f₂ ≫ h) y ⊤ c := by
    subst hc
    refine (gm_res f₂ y (V := ⊤) (U := h ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans ?_
    exact gm_pull f₂ h y ⊤ trivial c
  rw [map_mul, gmRP act₂ y W' _ le₂ hy, gmRP f₂ y ⊤ _ t₂ hy,
    gm_res act₂ y hW' hay, gm_pull act₂ a y W (hW' hay), e3]
  have e2 : gm (𝟙 P₂) y (s₂ ⁻¹ᵁ W') (pullU s₂ W' (res hW' (pullU a W u))) =
      gm (s₂ ≫ a) y W u := by
    rw [gm_pull (𝟙 P₂) s₂ y W' hsy, Category.id_comp, gm_res s₂ y hW' hsy,
      gm_pull s₂ a y W (hW' hsy)]
  rw [e2]
  exact o

end General

section Torus

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]

theorem charUnit_hTB (χ : X) :
    res (fun _ _ => trivial : (⊤ : (splitTorus S' X).left.Opens) ≤ hT f X ⁻¹ᵁ ⊤)
      (pullU (hT f X) ⊤ (charUnit S X χ)) = charUnit S' X χ := by
  let w := Units.map (Scheme.ΓSpecIso (torusRing ZU X)).inv.hom.toMonoidHom
    (Units.map (AddMonoidAlgebra.of ZU X) (toUnits (Multiplicative.ofAdd χ)))
  refine unit_ext fun x _ => ?_
  have e3 : hT f X ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) =
      pullback.fst (splitTorusAff ZU X).hom (toZ S') := pullback.lift_fst _ _ _
  have e1 : gm (𝟙 _) x ⊤ (charUnit S' X χ) =
      gm (pullback.fst (splitTorusAff ZU X).hom (toZ S')) x ⊤ w :=
    gmRP (pullback.fst (splitTorusAff ZU X).hom (toZ S')) x ⊤ ⊤ _ trivial w
  have e2 : gm (hT f X) x ⊤ (charUnit S X χ) =
      gm (hT f X ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S)) x ⊤ w :=
    (gm_res (hT f X) x (V := ⊤) (U := pullback.fst (splitTorusAff ZU X).hom (toZ S) ⁻¹ᵁ ⊤) _
      trivial _).trans (gm_pull _ _ x ⊤ trivial w)
  rw [e3] at e2
  exact (gmRP (hT f X) x ⊤ ⊤ _ trivial _).trans (e2.trans e1.symm)

end Torus

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] {G : Over S} [GrpObj G]

abbrev PQ : Over S := Over.mk ((splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f)

def uT : PQ f X (G := G) ⟶ splitTorus S X :=
  Over.homMk ((fst (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ hT f X) (by
    show _ ≫ _ ≫ (splitTorus S X).hom = (splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f
    rw [hT_snd, ← Category.assoc, Over.w (fst (splitTorus S' X) ((Over.pullback f).obj G))])

def vG : PQ f X (G := G) ⟶ G :=
  Over.homMk ((snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f) (by
    show _ ≫ _ ≫ G.hom = (splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd (splitTorus S' X) ((Over.pullback f).obj G))))

def bm : (splitTorus S' X ⊗ (Over.pullback f).obj G).left ⟶ (splitTorus S X ⊗ G).left :=
  (lift (uT f X) (vG f X)).left

lemma bm_snd : (snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f =
    bm f X ≫ (snd (splitTorus S X) G).left := by
  show _ = (lift (uT f X) (vG f X) ≫ snd _ _).left
  rw [lift_snd]
  rfl

lemma bm_fst : (fst (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ hT f X =
    bm f X ≫ (fst (splitTorus S X) G).left := by
  show _ = (lift (uT f X) (vG f X) ≫ fst _ _).left
  rw [lift_fst]
  rfl

lemma bm_act (i : splitTorus S X ⟶ G) :
    (lift (fst (splitTorus S' X) ((Over.pullback f).obj G) ≫ iB f X i)
        (snd (splitTorus S' X) ((Over.pullback f).obj G)) ≫ μ[(Over.pullback f).obj G]).left ≫
      pullback.fst G.hom f =
    bm f X ≫ (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left := by
  have hx : (lift (uT f X) (vG f X) ≫ fst (splitTorus S X) G ≫ i).left =
      (fst (splitTorus S' X) ((Over.pullback f).obj G) ≫ iB f X i).left ≫ pullback.fst G.hom f := by
    rw [← Category.assoc, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, iB_h]
    exact Category.assoc _ _ _
  have hy : (lift (uT f X) (vG f X) ≫ snd (splitTorus S X) G).left =
      (snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f := by
    rw [lift_snd]
    rfl
  have key := (isGrpPullback_pullback G f).2 _ _ _ _ _ hx hy
  rw [← Hom.mul_def, ← Hom.mul_def, ← key, ← MonObj.comp_mul]
  rfl

end Act

section Fields

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S) {G : Over S} [GrpObj G] (d : E.GtDatum G)

theorem actB_le : ∀ j : (pullExt f E).ChartIdx,
    (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⁻¹ᵁ
        ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ≤
      (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
        μ[(Over.pullback f).obj G]).left ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) := by
  haveI := d.q_hom
  haveI : IsMonHom (qB f d.q) :=
    isMonHom_of_grpPullback (isGrpPullback_pullback G f) (isGrpPullback_pullback E.B f) d.q
      (qB f d.q) (qB_h f d.q)
  intro j
  exact act_le_of_hom (qB f d.q) (iB f E.X d.i) (iB_isKernel f E.X d.q d.i d.isKernel).w _

theorem equivB : ∀ (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X),
    res (actB_le f E d j)
        (pullU (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
            μ[(Over.pullback f).obj G]).left _ (uB f E d j k)) =
      res (fun x _ => show (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left.base x ∈
          (⊤ : TopologicalSpace.Opens _) from trivial)
          (pullU (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⊤
            (charUnit S' (pullExt f E).X ((pullExt f E).basis k))) *
        pullU (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left _ (uB f E d j k) := by
  intro j k
  exact equivPullL (act₁ := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left)
    (s₁ := (snd (splitTorus S E.X) G).left) (f₁ := (fst (splitTorus S E.X) G).left)
    (act₂ := (lift (fst (splitTorus S' E.X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' E.X) ((Over.pullback f).obj G)) ≫ μ[(Over.pullback f).obj G]).left)
    (s₂ := (snd (splitTorus S' E.X) ((Over.pullback f).obj G)).left)
    (f₂ := (fst (splitTorus S' E.X) ((Over.pullback f).obj G)).left)
    (b := bm f E.X) (a := pullback.fst G.hom f) (h := hT f E.X)
    (W := d.q.left ⁻¹ᵁ E.chart (jj f E j)) (u := d.u (jj f E j) k)
    (W' := (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) (hW' := pre_le f E d j)
    (c := charUnit S E.X (E.basis k)) (c' := charUnit S' E.X (E.basis k))
    (hc := charUnit_hTB f E.X (E.basis k))
    (le₁ := d.act_le (jj f E j)) (t₁ := fun x _ => trivial)
    (H := d.equiv (jj f E j) k)
    (ha := bm_act f E.X d.i) (hs := bm_snd f E.X) (hf := bm_fst f E.X)
    (le₂ := actB_le f E d j) (t₂ := fun x _ => trivial)

end Fields

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
