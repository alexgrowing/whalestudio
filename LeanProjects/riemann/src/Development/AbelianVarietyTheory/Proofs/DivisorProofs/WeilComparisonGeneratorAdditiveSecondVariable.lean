import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem prod_cmp (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S} (a b : T ⟶ P₀.A) {V : Type} [CommGroup V]
    (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → V) :
    ∏ k, h ((lift a b).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k) ^ cmpε k =
      (h (((a ≫ f₂) * (b ≫ g₂)).left ≫ coprod.inr) * (h ((a ≫ f₂).left ≫ coprod.inr))⁻¹ *
        (h ((b ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
      (h (((a ≫ f₁) * (b ≫ g₁)).left ≫ coprod.inl) * (h ((a ≫ f₁).left ≫ coprod.inl))⁻¹ *
        (h ((b ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  have c₂ := prod_cube₂ (fst P₀.A P₀.A ≫ f₂) (snd P₀.A P₀.A ≫ g₂) (fun q => h ((lift a b).left ≫ q ≫ coprod.inr))
  have c₁ := prod_neg _ _ (prod_cube₂ (fst P₀.A P₀.A ≫ f₁) (snd P₀.A P₀.A ≫ g₁)
    (fun q => h ((lift a b).left ≫ q ≫ coprod.inl)))
  have e : ∀ {Q : Over S} (q : P₀.A ⊗ P₀.A ⟶ Q) (t : Q.left ⟶ P₁.A.left ⨿ P₂.A.left),
      (lift a b).left ≫ q.left ≫ t = (lift a b ≫ q).left ≫ t := fun q t => by rw [Over.comp_left, Category.assoc]
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) (c₂.trans ?_) (c₁.trans ?_)
  · simp only [e, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.comp_one]
  · simp only [e, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.comp_one]

end GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem add_snd : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x y y' : T ⟶ P₀.A), val u (lift x (y * y')).left z J * cubV c₁ z (rl J) (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (val u (lift x y).left z J * val u (lift x y').left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu hn T z J hJ x y y'
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have hL := join_isLB P₁.isLB P₂.isLB
  have pl := isPart_inl P₁.L P₂.L
  have pr := isPart_inr P₁.L P₂.L
  have vp : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : G3 P₀.A ⟶ P₀.A,
      val (LB.pullGen _ _ _ u (lift a b).left) σ.left z J = val u (lift (σ ≫ a) (σ ≫ b)).left z J :=
    fun σ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  let U₁ := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ u (lift p₀ (p₁ * p₂)).left)
    (pl.gen (LB.pullGen P₁.L _ _ c₁.t (lift (p₀ ≫ f₁) (lift (p₁ ≫ g₁) (p₂ ≫ g₁))).left))
  let U₂ := LB.mulGen _ _ _ _ _ (pr.gen (LB.pullGen P₂.L _ _ c₂.t (lift (p₀ ≫ f₂) (lift (p₁ ≫ g₂) (p₂ ≫ g₂))).left))
    (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ u (lift p₀ p₁).left) (LB.pullGen _ _ _ u (lift p₀ p₂).left))
  have hU₁ : U₁.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)
    (pl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _))
  have hU₂ : U₂.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (pr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
  have ev₁ : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val U₁ σ.left z J = val u (lift (σ ≫ p₀) (σ ≫ (p₁ * p₂))).left z J *
        cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ g₁) (σ ≫ p₂ ≫ g₁) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
      ((pl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (pl.good hJ) _ _ _)))
  have ev₂ : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val U₂ σ.left z J = cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ g₂) (σ ≫ p₂ ≫ g₂) *
        (val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J * val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((pr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (pr.good hJ) _ _ _))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o₁ : e ≫ (p₁ * p₂) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG P₀.isAb _) (surj_comp (surj_snd hG P₀.isAb _) (hG _ _ P₀.isAb).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hL (u := U₁) (u' := U₂) (fun V _ k => ?_) _ e.left he sj hU₁ hU₂ (fun w I hI => ?_)
  rotate_left
  · refine (prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
      (prod_cub (p₀ ≫ f₂) (p₁ ≫ g₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
      (prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₁ k)
        (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k))).trans
      (Eq.trans ?_ (prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ (p₁ * p₂) k)
        (prod_cub (p₀ ≫ f₁) (p₁ ≫ g₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    simp only [MonObj.mul_comp, ← _root_.mul_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [ev₁ e hI, ev₂ e hI]
    simp only [← Category.assoc, e₀, e₁, e₂, o₁, MonObj.one_comp]
    have C₁ := isCub_cubV c₁ (pl.good hI)
    have C₂ := isCub_cubV c₂ (pr.good hI)
    have v1 : val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) 1).left w I = 1 := by
      have eL : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) 1 = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
      rw [eL]
      exact (congrArg (fun q => val u q w I) (Category.id_comp _).symm).trans (hn _ (𝟙 _) w I hI)
    rw [v1, C₁.face, C₂.face]
    simp
  have kk := (ev₁ _ hJ).symm.trans ((key _ (lift x (lift y y')).left z J hJ).trans (ev₂ _ hJ))
  have r₀ : lift x (lift y y') ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y y') ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y y') ≫ p₂ = y' := by simp [p₂, x3]
  have s₁ : lift x (lift y y') ≫ (p₁ * p₂) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [r₁, r₂])
  rw [s₁] at kk
  simp only [← Category.assoc, r₀, r₁, r₂] at kk
  exact kk

end GlobalTheory.Mum.Two.WeilCmp
