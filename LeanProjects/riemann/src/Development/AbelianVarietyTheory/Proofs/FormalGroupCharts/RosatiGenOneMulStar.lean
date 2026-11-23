import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf

noncomputable section

namespace GlobalTheory

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem genUniqueSq (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J) (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ A).left) (z : Z)
    (J) (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF (A ⊗ A).hom _ (Over.w _) hs hu hu' h Z r z J hJ

theorem rosatiGen_swap (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) (f g f' g' : A ⟶ A)
    (ef : f' = g) (eg : g' = f)
    (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (h₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L))
    (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f' g') rosatiε)) (h₂ : u₂.IsGen)
    (n₂ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x y : T ⟶ A) : val₂ u₂ z J x y = (val₂ u₁ z J y x)⁻¹ := by
  subst ef eg
  have key := genUniqueSq hs hL (fun U _ k => by
      refine (DVR.prod_neg _ _ (prod_ros g' f' (snd A A) (fst A A) k)).trans
        (Eq.trans ?_ (prod_ros f' g' (fst A A) (snd A A) k).symm)
      rw [mul_comm (snd A A ≫ g'), mul_comm (snd A A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (DVR.pullGen_isGen _ _ _ _ h₂ (lift (fst A A) (snd A A)).left)
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₁ (lift (snd A A) (fst A A)).left)) (fun y I hI => by
      rw [val_inv, DVR.val_ros _ _ hI, DVR.val_ros _ _ hI, lift_fst, lift_snd, DVR.val₂_one n₁ hI,
        DVR.val₂_one n₂ hI, inv_one])
    _ (lift x y).left z J hJ
  rwa [val_inv, DVR.val_ros _ _ hJ, DVR.val_ros _ _ hJ, lift_fst, lift_snd] at key

theorem rosatiGen_comp (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) (f g f' g' F H : A ⟶ A)
    [IsMonHom f'] [IsMonHom g] (eF : F = f' ≫ f) (eH : H = g ≫ g')
    (u : LB.Gen (LB.LinComb L (rosatiφ A F H) rosatiε)) (h : u.IsGen)
    (n : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (h₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L))
    (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f' g') rosatiε)) (h₂ : u₂.IsGen)
    (n₂ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) (x y : T ⟶ A) :
    val₂ u z J x y = val₂ u₁ z J (x ≫ f') y * val₂ u₂ z J x (y ≫ g) := by
  subst eF eH
  have key := genUniqueSq hs hL (fun U _ k => by
      refine (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros f g (fst A A ≫ f') (snd A A) k)
        (prod_ros f' g' (fst A A) (snd A A ≫ g) k)).trans
        (Eq.trans ?_ (prod_ros (f' ≫ f) (g ≫ g') (fst A A) (snd A A) k).symm)
      rw [Category.assoc, Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (DVR.pullGen_isGen _ _ _ _ h (lift (fst A A) (snd A A)).left)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₁ (lift (fst A A ≫ f') (snd A A)).left)
      (DVR.pullGen_isGen _ _ _ _ h₂ (lift (fst A A) (snd A A ≫ g)).left)) (fun y I hI => by
      rw [val_mul hI, DVR.val_ros _ _ hI, DVR.val_ros _ _ hI, DVR.val_ros _ _ hI, lift_fst_assoc, lift_snd_assoc,
        lift_fst, lift_snd, MonObj.one_comp, MonObj.one_comp, DVR.val₂_one n hI, DVR.val₂_one n₁ hI,
        DVR.val₂_one n₂ hI, _root_.mul_one])
    _ (lift x y).left z J hJ
  rwa [val_mul hJ, DVR.val_ros _ _ hJ, DVR.val_ros _ _ hJ, DVR.val_ros _ _ hJ, lift_fst_assoc, lift_snd_assoc,
    lift_fst, lift_snd] at key

end

theorem rosatiGen_one_mul_star : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ x y : T ⟶ G, val₂ (u 1) z J x y = 1) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a * b)) z J x y = val₂ (u a) z J (x ≫ act.act b) y * val₂ (u b) z J x (y ≫ act.act (star a))) ∧ (∀ (a : O) (x y : T ⟶ G), val₂ (u a) z J x y * val₂ (u (star a)) z J y x = 1) := by
  intro S G _ _ hs _ Lr _ O _ _ act u hu T z J hJ
  have hm : ∀ (a b : O) (x y : T ⟶ G), val₂ (u (a * b)) z J x y =
      val₂ (u a) z J (x ≫ act.act b) y * val₂ (u b) z J x (y ≫ act.act (star a)) := fun a b x y => by
    have := act.hom b
    have := act.hom (star a)
    exact rosatiGen_comp hs Lr.isLB _ _ _ _ _ _ (by rw [mul_comm, act.mul]) (by rw [star_mul', act.mul])
      _ (hu _).1 (hu _).2 _ (hu a).1 (hu a).2 _ (hu b).1 (hu b).2 hJ x y
  refine ⟨fun x y => ?_, hm, fun a x y => ?_⟩
  · have h := hm 1 1 x y
    have e : val₂ (u (1 * 1)) z J x y = val₂ (u 1) z J x y :=
      congrArg (fun a => val₂ (u a) z J x y) (_root_.mul_one 1)
    have e₁ : x ≫ act.act 1 = x := by rw [act.one, Category.comp_id]
    have e₂ : y ≫ act.act (star 1) = y := by rw [star_one, act.one, Category.comp_id]
    rw [e, e₁, e₂] at h
    exact mul_eq_left.1 h.symm
  · rw [rosatiGen_swap hs Lr.isLB _ _ _ _ rfl (by rw [star_star]) _ (hu a).1 (hu a).2 _ (hu (star a)).1
      (hu (star a)).2 hJ y x, mul_inv_cancel]

end GlobalTheory
