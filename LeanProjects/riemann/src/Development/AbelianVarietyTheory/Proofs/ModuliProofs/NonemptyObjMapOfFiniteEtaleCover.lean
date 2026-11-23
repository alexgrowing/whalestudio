import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjDescent

theorem isGrpPullback_id {S S₂ : Scheme.{0}} {G G' : Over S} {G₂ : Over S₂} [GrpObj G] [GrpObj G'] [GrpObj G₂]
    {q : S₂ ⟶ S} [Flat q] [Surjective q] {a : G₂.left ⟶ G.left} {c : G₂.left ⟶ G'.left}
    (h : IsGrpPullback G₂ G q a) (h' : IsGrpPullback G₂ G' q c) (φ : G.left ⟶ G'.left) [IsIso φ] (e : a ≫ φ = c)
    (w : φ ≫ G'.hom = G.hom ≫ 𝟙 S) : IsGrpPullback G G' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨w⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let r := pullback.fst T.hom q
  have : Epi r := Flat.epi_of_flat_of_surjective _
  let T' : Over S₂ := Over.mk (pullback.snd T.hom q)
  have up : ∀ z : T ⟶ G, ∃ z' : T' ⟶ G₂, r ≫ z.left = z'.left ≫ a := fun z =>
    ⟨Over.homMk (h.1.lift (r ≫ z.left) (pullback.snd T.hom q)
      (by rw [Category.assoc, Over.w z]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      (h.1.lift_fst _ _ _).symm⟩
  obtain ⟨x', hx'⟩ := up x
  obtain ⟨y', hy'⟩ := up y
  let R : Over.mk (T'.hom ≫ q) ⟶ T := Over.homMk r pullback.condition
  let R' : Over.mk (T'.hom ≫ q) ⟶ Over.mk (T.hom ≫ 𝟙 S) :=
    Over.homMk r ((congrArg (r ≫ ·) (Category.comp_id T.hom)).trans pullback.condition)
  have e₁ := h.2 T' x' y' (R ≫ x) (R ≫ y) hx' hy'
  have e₂ := h'.2 T' x' y' (R' ≫ x₀) (R' ≫ y₀)
    (by show r ≫ x₀.left = _; rw [hx, ← Category.assoc, hx', Category.assoc, e])
    (by show r ≫ y₀.left = _; rw [hy, ← Category.assoc, hy', Category.assoc, e])
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← cancel_epi r, ← Category.assoc]
  refine e₂.trans ?_
  rw [← e, ← Category.assoc]
  exact congrArg (· ≫ φ) e₁.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S₂ : Scheme.{0}} {s : S ⟶ Sp B} {s' : S ⟶ Sp B'} {s'' : S₂ ⟶ Sp B''}
  {u : Obj D l b s} {ob : Obj D l b' s'} {ob₂ : Obj D l b'' s''} {q : S₂ ⟶ S}

theorem exists_congr {q' : S₂ ⟶ S} (e : q = q') (m : ObjMap ob₂ ob q) :
    ∃ m' : ObjMap ob₂ ob q', m'.toSABMap.φ = m.toSABMap.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem comp_eq_of_comp_eq (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ ob₂.t.G.left) (h : g₁ ≫ m.toSABMap.φ = g₂ ≫ m.toSABMap.φ) :
    g₁ ≫ n.toSABMap.φ = g₂ ≫ n.toSABMap.φ := by
  have hp : (g₁ ≫ ob₂.t.G.hom) ≫ q = (g₂ ≫ ob₂.t.G.hom) ≫ q := by
    rw [Category.assoc, Category.assoc, ← m.cart.1.w, ← Category.assoc, h, Category.assoc]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l B'' B'' b'' b'' (RingHom.id _) S₂ Z s'' ((g₁ ≫ ob₂.t.G.hom) ≫ s'')
    (g₁ ≫ ob₂.t.G.hom) rfl rfl ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) ob₂
  obtain ⟨k, hk⟩ := ObjComp.objMap_comp m m₁
  obtain ⟨k', hk'⟩ := exists_congr hp k
  obtain ⟨m₂, hm₂⟩ := ObjComp.objMap_cancel m k'
  obtain ⟨n₁, hn₁⟩ := ObjComp.objMap_comp n m₁
  obtain ⟨n₁', hn₁'⟩ := exists_congr hp n₁
  obtain ⟨n₂, hn₂⟩ := ObjComp.objMap_comp n m₂
  have e := obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ _ _ _ _ u o _
    n₁'.toSABMap n₂.toSABMap fun a => ⟨_, n₁'.eta a, n₂.eta a⟩
  rw [hn₁', hn₁, hn₂] at e
  rw [hk', hk] at hm₂
  let σ := m₁.cart.1.lift g₁ (𝟙 Z) (Category.id_comp _).symm
  have h₁ : σ ≫ m₁.toSABMap.φ = g₁ := m₁.cart.1.lift_fst _ _ _
  have h₀ : σ ≫ o.t.G.hom = 𝟙 Z := m₁.cart.1.lift_snd _ _ _
  have h₂ : σ ≫ m₂.toSABMap.φ = g₂ := by
    apply m.cart.1.hom_ext
    · rw [Category.assoc]
      refine (congrArg (σ ≫ ·) hm₂.symm).trans ?_
      rw [← Category.assoc, h₁, h]
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, h₀, Category.id_comp]
  refine (congrArg (· ≫ n.toSABMap.φ) h₁).symm.trans (Eq.trans ?_ (congrArg (· ≫ n.toSABMap.φ) h₂))
  exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) e).trans (Category.assoc _ _ _).symm)

variable [Flat q] [Surjective q] [QuasiCompact q]

theorem effectiveEpi (m : ObjMap ob₂ ob q) : EffectiveEpi m.toSABMap.φ := by
  have : Flat m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  infer_instance

theorem exists_fac (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    ∃ φ : ob.t.G.left ⟶ u.t.G.left, m.toSABMap.φ ≫ φ = n.toSABMap.φ :=
  have := effectiveEpi m
  ⟨EffectiveEpi.desc m.toSABMap.φ n.toSABMap.φ (comp_eq_of_comp_eq hL m n), EffectiveEpi.fac _ _ _⟩

theorem nonempty_objMap_id (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    Nonempty (ObjMap ob u (𝟙 S)) := by
  obtain ⟨φ, hφ⟩ := exists_fac hL m n
  obtain ⟨ψ, hψ⟩ := exists_fac hL n m
  have := effectiveEpi m
  have := effectiveEpi n
  have : Epi q := Flat.epi_of_flat_of_surjective _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, hψ, Category.comp_id],
    by rw [← cancel_epi n.toSABMap.φ, ← Category.assoc, hψ, hφ, Category.comp_id]⟩
  have w : φ ≫ u.t.G.hom = ob.t.G.hom ≫ 𝟙 S := by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, Category.comp_id, m.cart.1.w, n.cart.1.w]
  have gp : IsGrpPullback ob.t.G u.t.G (𝟙 S) φ := isGrpPullback_id m.cart n.cart φ hφ w
  have hact : ∀ a, (ob.t.act.act a).left ≫ φ = φ ≫ (u.t.act.act a).left := fun a => by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, ← m.act, Category.assoc, hφ, n.act, ← Category.assoc, hφ]
  have hiso : LBIso ob.t.PP.L (u.t.PP.L.pull φ) := by
    have h₁ := ob.t.PP.isLB
    have h₂ := pull_isLB u.t.PP.isLB φ
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ u.t.PP.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have cl : ∀ {t : SAB H S} (k : SABMap ob₂.t t q),
        CechPic.cls _ ob₂.t.PP.isLB = CechPic.pull k.φ (CechPic.cls _ t.PP.isLB) := fun {t} k => by
      obtain ⟨w, hw, -⟩ := k.lin
      exact (CechPic.cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have z : ∀ t : SAB H S, CechPic.pull (eSec t.G) (CechPic.cls _ t.PP.isLB) = 0 := fun t =>
      (CechPic.cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange hL.globalFns S S₂ q ob.t.G _ (ObjDim.isAbelianScheme ob) hN inferInstance inferInstance
      inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have he : eSec ob.t.G ≫ φ = 𝟙 S ≫ eSec u.t.G := (cubeMapOf gp).e_comm
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, z, he, Category.id_comp, z, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← m.cart.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp,
        hφ, ← cl, ← cl, sub_self, map_zero]
  obtain ⟨k, hk⟩ := exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S u.t ob.t (𝟙 S) φ u.proper gp hiso hact
  have key : ∀ (σ₂ : S₂ ⟶ ob₂.t.G.left) (σ : S ⟶ ob.t.G.left) (τ : S ⟶ u.t.G.left),
      σ₂ ≫ m.toSABMap.φ = q ≫ σ → σ₂ ≫ n.toSABMap.φ = q ≫ τ → σ ≫ k.φ = 𝟙 S ≫ τ := fun σ₂ σ τ h₁ h₂ => by
    rw [← cancel_epi q, hk, Category.id_comp, ← Category.assoc, ← h₁, ← h₂, Category.assoc, hφ]
  exact ⟨⟨k, fun a => key _ _ _ (m.eta a) (n.eta a), fun a => key _ _ _ (m.etaA a) (n.etaA a)⟩⟩

end GlobalTheory.ObjDescent

namespace GlobalTheory

theorem nonempty_objMap_of_finite_etale_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  intro hL _ E _ _ _ H D l B B' B'' _ _ _ b b' b'' X S S₂ s s' s'' u ob ob₂ q f _ _ _ _ ⟨m⟩ ⟨n⟩
  obtain ⟨u', ⟨p⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) X S s (f ≫ s) f rfl rfl
    ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) u
  obtain ⟨n', -⟩ := ObjComp.objMap_cancel p n
  obtain ⟨k⟩ := ObjDescent.nonempty_objMap_id hL m n'
  obtain ⟨k', -⟩ := ObjComp.objMap_comp p k
  obtain ⟨k'', -⟩ := ObjDescent.exists_congr (Category.id_comp f) k'
  exact ⟨k''⟩

end GlobalTheory
