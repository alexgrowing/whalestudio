import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp.AddFst

theorem prod_pair {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] (f g : A ⟶ B) {T : Over S} (x y : T ⟶ A)
    {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card)) =
      h ((x ≫ f) * (y ≫ g)).left * (h (x ≫ f).left)⁻¹ * (h (y ≫ g).left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I).left =
      (psum B ![x ≫ f, y ≫ g] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) ![fst A A ≫ f, snd A A ≫ g] I).trans
      (congrArg (fun q => psum B q I) (funext fun i => by fin_cases i <;> simp [preHom])))
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum B ![x ≫ f, y ≫ g] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I.down)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum B ![x ≫ f, y ≫ g] ∅ = 1 := rfl
  have p₁ : psum B ![x ≫ f, y ≫ g] {0} = x ≫ f := _root_.mul_one (x ≫ f)
  have p₂ : psum B ![x ≫ f, y ≫ g] {1} = y ≫ g := _root_.mul_one (y ≫ g)
  have p₃ : psum B ![x ≫ f, y ≫ g] {0, 1} = (x ≫ f) * (y ≫ g) := congrArg ((x ≫ f) * ·) (_root_.mul_one (y ≫ g))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_cmp {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S}
    (x y : T ⟶ P₀.A) {U : Type} [CommGroup U] (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → U) :
    ∏ i, h ((lift x y).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ i) ^ cmpε i =
      (h (((x ≫ f₂) * (y ≫ g₂)).left ≫ coprod.inr) * (h ((x ≫ f₂).left ≫ coprod.inr))⁻¹ *
          (h ((y ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
        (h (((x ≫ f₁) * (y ≫ g₁)).left ≫ coprod.inl) * (h ((x ≫ f₁).left ≫ coprod.inl))⁻¹ *
          (h ((y ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  refine DVR.prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (prod_pair f₂ g₂ x y fun q => h (q ≫ coprod.inr))
    rw [Category.assoc]; rfl
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (DVR.prod_neg _ _ (prod_pair f₁ g₁ x y fun q => h (q ≫ coprod.inl)))
    rw [Category.assoc]; rfl

theorem cmp_add_fst : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x x' y : T ⟶ P₀.A), val u (lift (x * x') y).left z J * cubV c₁ z (rl J) (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (val u (lift x y).left z J * val u (lift x' y).left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu h₀ T z J hJ x x' y
  have hA := P₀.isAb
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : T ⟶ P₀.A,
      val (LB.pullGen (join P₁.L P₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good (join P₁.L P₂.L) y J →
      val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A)).left y J = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A) = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
    have := h₀ _ (𝟙 S) y J hJ
    rw [e]
    exact (congrArg (fun q => val u q y J) (Category.id_comp _)).symm.trans this
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  let ρ : T ⟶ G3 P₀.A := lift x (lift x' y)
  have s₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have s₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have s₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have o₂ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [s₀, s₁])
  have hl := isPart_inl P₁.L P₂.L
  have hr := isPart_inr P₁.L P₂.L
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift (p₀ * p₁) p₂).left)
        (hl.gen (LB.pullGen P₁.L (thφ P₁.A (x3 P₁.A)) thε c₁.t
          (lift (p₀ ≫ f₁) (lift (p₁ ≫ f₁) (p₂ ≫ g₁))).left))) σ.left z J =
        val u (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J *
          cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ f₁) (σ ≫ p₂ ≫ g₁) ∧
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (hr.gen (LB.pullGen P₂.L (thφ P₂.A (x3 P₂.A)) thε c₂.t
          (lift (p₀ ≫ f₂) (lift (p₁ ≫ f₂) (p₂ ≫ g₂))).left))
        (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₀ p₂).left)
          (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₁ p₂).left))) σ.left z J =
        cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ f₂) (σ ≫ p₂ ≫ g₂) *
          (val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val u (lift (σ ≫ p₁) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
        ((hl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (hl.good hJ) _ _ _))),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((hr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (hr.good hJ) _ _ _))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
  have key := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' (join_isLB P₁.isLB P₂.isLB) (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (hl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _)) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
  · simp only [← Category.assoc] at key
    rwa [o₂, s₀, s₁, s₂] at key
  · refine (DVR.prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
        (prod_cub (p₀ ≫ f₂) (p₁ ≫ f₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
        (DVR.prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k)
          (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₁ p₂ k))).trans
        (Eq.trans ?_ (DVR.prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (p₀ * p₁) p₂ k)
          (prod_cub (p₀ ≫ f₁) (p₁ ≫ f₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    rw [MonObj.mul_comp p₀ p₁ f₁, MonObj.mul_comp p₀ p₁ f₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C₁ := isCub_cubV c₁ (hl.good hI)
    have C₂ := isCub_cubV c₂ (hr.good hI)
    refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
    rw [← Category.assoc e p₀, ← Category.assoc e p₀, o₁, e₀, e₁, e₂, MonObj.one_comp, MonObj.one_comp, v1 hI]
    rw [C₁.face, C₂.face]
    simp

end GlobalTheory.Mum.Two.WeilCmp.AddFst
