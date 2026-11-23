import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

namespace ModelDimension.Tan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom preHom)

variable {R : Type} [CommRing R]

abbrev sc {S : Scheme.{0}} (x : Spec (CommRingCat.of R) ⟶ S) (c : R) : epsAt x ⟶ epsAt x :=
  LieEx.hom x (c • (LinearMap.id : R →ₗ[R] R))

theorem sc_left {S : Scheme.{0}} (x : Spec (CommRingCat.of R) ⟶ S) (c : R) :
    (sc x c).left = Spec.map (CommRingCat.ofHom (epsMul c)) := rfl

structure Corr {S₁ S₂ : Scheme.{0}} (G₁ : Over S₁) (G₂ : Over S₂) [GrpObj G₁] [GrpObj G₂] {O : Type}
    (a₁ : O → (G₁ ⟶ G₁)) (a₂ : O → (G₂ ⟶ G₂)) (x₁ : Spec (CommRingCat.of R) ⟶ S₁)
    (x₂ : Spec (CommRingCat.of R) ⟶ S₂) where

  e : (epsAt x₁ ⟶ G₁) ≃* (epsAt x₂ ⟶ G₂)
  tan : ∀ v, IsTanAt G₂ x₂ (e v) ↔ IsTanAt G₁ x₁ v
  act : ∀ a v, e (v ≫ a₁ a) = e v ≫ a₂ a
  scale : ∀ c v, e (sc x₁ c ≫ v) = sc x₂ c ≫ e v

section Corr

variable {S₁ S₂ S₃ : Scheme.{0}} {G₁ : Over S₁} {G₂ : Over S₂} {G₃ : Over S₃} [GrpObj G₁] [GrpObj G₂] [GrpObj G₃]
  {O : Type} {a₁ : O → (G₁ ⟶ G₁)} {a₂ : O → (G₂ ⟶ G₂)} {a₃ : O → (G₃ ⟶ G₃)}
  {x₁ : Spec (CommRingCat.of R) ⟶ S₁} {x₂ : Spec (CommRingCat.of R) ⟶ S₂} {x₃ : Spec (CommRingCat.of R) ⟶ S₃}

def Corr.symm (C : Corr G₁ G₂ a₁ a₂ x₁ x₂) : Corr G₂ G₁ a₂ a₁ x₂ x₁ where
  e := C.e.symm
  tan v := by rw [← C.tan, MulEquiv.apply_symm_apply]
  act a v := C.e.injective (by rw [C.act, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])
  scale c v := C.e.injective (by rw [C.scale, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])

def Corr.trans (C : Corr G₁ G₂ a₁ a₂ x₁ x₂) (D : Corr G₂ G₃ a₂ a₃ x₂ x₃) : Corr G₁ G₃ a₁ a₃ x₁ x₃ where
  e := C.e.trans D.e
  tan v := (D.tan _).trans (C.tan v)
  act a v := by rw [MulEquiv.trans_apply, MulEquiv.trans_apply, C.act, D.act]
  scale c v := by rw [MulEquiv.trans_apply, MulEquiv.trans_apply, C.scale, D.scale]

variable {f : S₁ ⟶ S₂} {φ : G₁.left ⟶ G₂.left}

theorem mul_push (h : IsGrpPullback G₁ G₂ f φ) {Z : Scheme.{0}} {a : Z ⟶ S₁} {b : Z ⟶ S₂} (hab : a ≫ f = b)
    (x y : Over.mk a ⟶ G₁) (x₀ y₀ : Over.mk b ⟶ G₂) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hab
  exact h.2 (Over.mk a) x y x₀ y₀ hx hy

theorem one_push (h : IsGrpPullback G₁ G₂ f φ) {Z : Scheme.{0}} {a : Z ⟶ S₁} {b : Z ⟶ S₂} (hab : a ≫ f = b) :
    (1 : Over.mk b ⟶ G₂).left = (1 : Over.mk a ⟶ G₁).left ≫ φ := by
  subst hab
  exact (congrArg (fun z => z.left) (map_one (pushHom h (Over.mk a)))).symm

theorem exists_corr (h : IsGrpPullback G₁ G₂ f φ) (hact : ∀ a, (a₁ a).left ≫ φ = φ ≫ (a₂ a).left)
    (hx : x₁ ≫ f = x₂) : ∃ C : Corr G₁ G₂ a₁ a₂ x₁ x₂, ∀ v, (C.e v).left = v.left ≫ φ := by
  have hb : (epsAt x₁).hom ≫ f = (epsAt x₂).hom := by
    rw [← hx]; exact Category.assoc _ _ _
  have w1 : ∀ v : epsAt x₁ ⟶ G₁, (v.left ≫ φ) ≫ G₂.hom = (epsAt x₂).hom := fun v => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v, hb]
  have w2 : ∀ p : epsAt x₂ ⟶ G₂, p.left ≫ G₂.hom = (epsAt x₁).hom ≫ f := fun p => (Over.w p).trans hb.symm
  let F : (epsAt x₁ ⟶ G₁) → (epsAt x₂ ⟶ G₂) := fun v => Over.homMk (v.left ≫ φ) (w1 v)
  have hF : ∀ v, (F v).left = v.left ≫ φ := fun _ => rfl
  have hinj : Function.Injective F := fun v v' e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w v).trans (Over.w v').symm))
  have hsurj : Function.Surjective F := fun p =>
    ⟨Over.homMk (h.1.lift p.left (epsAt x₁).hom (w2 p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  have hmul : ∀ v v', F (v * v') = F v * F v' := fun v v' => Over.OverMorphism.ext
    (mul_push h hb v v' (F v) (F v') rfl rfl).symm
  refine ⟨⟨MulEquiv.mk' (Equiv.ofBijective F ⟨hinj, hsurj⟩) hmul, fun v => ?_, fun a v => ?_, fun c v => ?_⟩, hF⟩
  · have h1 := one_push h hx
    constructor
    · intro hv
      have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left ≫ φ =
          (1 : Over.mk x₂ ⟶ G₂).left := hv
      refine h.1.hom_ext (((Category.assoc _ _ _).trans hv').trans h1) ?_
      exact (Over.w ((LieEx.zsec x₁ : _ ⟶ LieEx.ob x₁ R) ≫ v)).trans (Over.w (1 : Over.mk x₁ ⟶ G₁)).symm
    · intro hv
      have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left =
          (1 : Over.mk x₁ ⟶ G₁).left := hv
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) hv')).trans h1.symm
  · refine Over.OverMorphism.ext ?_
    change (v.left ≫ (a₁ a).left) ≫ φ = (v.left ≫ φ) ≫ (a₂ a).left
    rw [Category.assoc, Category.assoc, hact]
  · exact Over.OverMorphism.ext (Category.assoc _ _ _)

end Corr

section Span

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {F : Type} [CommRing F]

theorem pt_sum {x : Spec (CommRingCat.of F) ⟶ X} {Li : Type} [AddCommGroup Li] [Module F Li]
    (M : LieModel G x Li) {r : ℕ} (g : Fin r → Li) : M.pt (∑ i, g i) = (List.ofFn fun i => M.pt (g i)).prod := by
  have h0 : M.pt 0 = 1 := by
    have := M.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hl : ∀ l : List Li, M.pt l.sum = (l.map M.pt).prod := fun l => by
    induction l with
    | nil => simpa using h0
    | cons a l ih => simp [M.add, ih]
  rw [← List.sum_ofFn, hl, List.map_ofFn]
  rfl

theorem mem_eigSp {Li : Type} [AddCommGroup Li] [Module F Li] {O : Type} [CommRing O]
    (ρ : O →+* Module.End F Li) (σ : O →+* F) (w : Li) : w ∈ eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem sc_epsHom (ψ : R →+* F) (z : Spec (CommRingCat.of R) ⟶ X) (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : Spec.map (CommRingCat.ofHom ψ) ≫ z = x) (c : R) :
    sc x (ψ c) ≫ LieCarrier.epsHom ψ z x hx = LieCarrier.epsHom ψ z x hx ≫ sc z c := by
  refine Over.OverMorphism.ext ?_
  change Spec.map (CommRingCat.ofHom (epsMul (ψ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap ψ)) =
    Spec.map (CommRingCat.ofHom (dualMap ψ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    LieCarrier.dualMap_epsMul]

theorem isTanAt_sc {z : Spec (CommRingCat.of R) ⟶ X} {v : epsAt z ⟶ G} (hv : IsTanAt G z v) (c : R) :
    IsTanAt G z (sc z c ≫ v) := by
  rw [LieEx.isTanAt_iff] at hv ⊢
  rw [← Category.assoc, LieEx.zsec_hom]
  exact hv

variable [IsCommMonObj G] [Algebra R F]

theorem span_eig (hinj : Function.Injective (algebraMap R F)) (z : Spec (CommRingCat.of R) ⟶ X)
    (x : Spec (CommRingCat.of F) ⟶ X) (hx : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ z = x)
    {Li : Type} [AddCommGroup Li] [Module F Li] [Module R Li] [IsScalarTower R F Li] (M : LieModel G x Li)
    {O : Type} [CommRing O] (act : O → (G ⟶ G)) (hA : ∀ a, IsMonHom (act a)) (ρ : O →+* Module.End F Li)
    (hρ : M.IsActOf act ρ) (σ : O →+* R) (σ' : O →+* F) (hσ : ∀ a, σ' a = algebraMap R F (σ a))
    {r : ℕ} (ub : Fin r → (epsAt z ⟶ G)) (hut : ∀ i, IsTanAt G z (ub i))
    (hue : ∀ i a, ub i ≫ act a = sc z (σ a) ≫ ub i)
    (hub : ∀ v : epsAt z ⟶ G, IsTanAt G z v → (∀ a, v ≫ act a = sc z (σ a) ≫ v) →
      ∃ cf : Fin r → R, v = (List.ofFn fun i => sc z (cf i) ≫ ub i).prod) :
    ∃ w : Fin r → Li, (∀ i, (M.pt (w i)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R F))) ≫ (ub i).left) ∧
      ∀ e : Li, ((∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
        (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R F))) ≫ v.left) ∧ e ∈ eigSp ρ σ') ↔
        e ∈ Submodule.span R (Set.range w) := by
  let j : epsAt x ⟶ epsAt z := LieCarrier.epsHom (algebraMap R F) z x hx
  have hj : ∀ c, sc x (algebraMap R F c) ≫ j = j ≫ sc z c := sc_epsHom _ z x hx
  have hsm : ∀ (c : F) e, M.pt (c • e) = sc x c ≫ M.pt e := fun c e => Over.OverMorphism.ext (M.smul c e)
  have hw : ∀ i, ∃ w, M.pt w = j ≫ ub i := fun i => M.onto _ (LieFib.isTanAt_epsHom _ _ _ _ _ (hut i))
  choose w hw using hw
  have key : ∀ cf : Fin r → R, M.pt (∑ i, cf i • w i) = j ≫ (List.ofFn fun i => sc z (cf i) ≫ ub i).prod := by
    intro cf
    rw [pt_sum]
    refine Eq.trans ?_ (map_list_prod (preHom (G := G) j) _).symm
    rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    change M.pt (cf i • w i) = j ≫ sc z (cf i) ≫ ub i
    rw [← algebraMap_smul F (cf i) (w i), hsm, hw, ← Category.assoc, hj, Category.assoc]
  refine ⟨w, fun i => congrArg (fun q => q.left) (hw i), fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨v, hvT, hv⟩, hE⟩
    have hv' : M.pt e = j ≫ v := Over.OverMorphism.ext hv
    have hE' := (mem_eigSp ρ _ e).1 hE
    have hv1 : ∀ a, v ≫ act a = sc z (σ a) ≫ v := by
      intro a
      haveI := hA a
      refine LieCarrier.tan_ext _ hinj z _ _ ((LieEx.isTanAt_iff _ _ _).2 ?_) (isTanAt_sc hvT _) ?_
      · rw [← Category.assoc, (LieEx.isTanAt_iff _ _ _).1 hvT, one_comp]
      · have e1 : j ≫ v ≫ act a = j ≫ sc z (σ a) ≫ v := by
          rw [← Category.assoc, ← hv', ← hρ a e, hE' a, hsm, hσ, hv', ← Category.assoc, hj, Category.assoc]
        exact congrArg (fun q => q.left) e1
    obtain ⟨cf, hcf⟩ := hub v hvT hv1
    have : e = ∑ i, cf i • w i := M.inj (by rw [key, hv', ← hcf])
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    refine ⟨⟨(List.ofFn fun i => sc z (cf i) ≫ ub i).prod, (LieEx.isTanAt_iff _ _ _).2 ?_,
      congrArg (fun q => q.left) (key cf)⟩, Submodule.sum_mem _ fun i _ => ?_⟩
    · refine (LieEx.tanSub z G).list_prod_mem fun v hv => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact (LieEx.isTanAt_iff _ _ _).1 (isTanAt_sc (hut i) _)
    · rw [← algebraMap_smul F (cf i) (w i)]
      refine Submodule.smul_mem _ _ ((mem_eigSp ρ _ _).2 fun a => M.inj ?_)
      rw [hρ a, hsm, hw, hσ, ← Category.assoc, hj, Category.assoc, Category.assoc, hue]

end Span

end ModelDimension.Tan
