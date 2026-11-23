import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {R : Type} [CommRing R]

def pushAt (h : IsGrpPullback G' G f φ) {T : Over S'} (v : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    change (v.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v])

theorem pushAt_one (h : IsGrpPullback G' G f φ) (T : Over S') : pushAt h (1 : T ⟶ G') = 1 := by
  have e : pushAt h (1 : T ⟶ G') * pushAt h (1 : T ⟶ G') = pushAt h (1 : T ⟶ G') := by
    apply Over.OverMorphism.ext
    have := h.2 T 1 1 (pushAt h 1) (pushAt h 1) rfl rfl
    rw [this, _root_.mul_one]
    rfl
  exact mul_eq_left.mp e

def tanMap (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') : epsAt (y ≫ f) ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    change (v.left ≫ φ) ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ y ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc]
    have := Over.w v
    change v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y at this
    rw [this, Category.assoc])

@[simp] theorem tanMap_left (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    (tanMap h y v).left = v.left ≫ φ := rfl

def rebase₂ (y : Sp R ⟶ S') (f : S' ⟶ S) : epsAt (y ≫ f) ⟶ Over.mk ((epsAt y).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (spMap (algebraMap R (DualNumber R)) ≫ y) ≫ f = spMap (algebraMap R (DualNumber R)) ≫ y ≫ f
    rw [Category.id_comp, Category.assoc])

theorem tanMap_eq (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    tanMap h y v = rebase₂ y f ≫ pushAt h v := by
  apply Over.OverMorphism.ext
  change v.left ≫ φ = 𝟙 _ ≫ v.left ≫ φ
  rw [Category.id_comp]

theorem tanMap_mul (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (a b : epsAt y ⟶ G') :
    tanMap h y (a * b) = tanMap h y a * tanMap h y b := by
  rw [tanMap_eq, tanMap_eq, tanMap_eq, ← MonObj.comp_mul]
  congr 1
  apply Over.OverMorphism.ext
  exact (h.2 _ a b (pushAt h a) (pushAt h b) rfl rfl).symm

theorem tanMap_one (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') :
    tanMap h y (1 : epsAt y ⟶ G') = 1 := by
  rw [tanMap_eq, pushAt_one, Hom.one_def, Hom.one_def, ← Category.assoc,
    toUnit_unique (rebase₂ y f ≫ toUnit _) (toUnit _)]

theorem left_eq_of_comp (h : IsGrpPullback G' G f φ) {Z : Scheme.{0}} {a b : Z ⟶ G'.left}
    (h₁ : a ≫ φ = b ≫ φ) (h₂ : a ≫ G'.hom = b ≫ G'.hom) : a = b :=
  h.1.hom_ext h₁ h₂

theorem tanMap_injective (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') : Function.Injective (tanMap h y) := by
  intro a b e
  apply Over.OverMorphism.ext
  refine left_eq_of_comp h (congrArg (fun z => z.left) e) ?_
  rw [Over.w a, Over.w b]

theorem tanMap_surjective (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') : Function.Surjective (tanMap h y) := by
  intro w
  have hw : w.left ≫ G.hom = (spMap (algebraMap R (DualNumber R)) ≫ y) ≫ f := by
    rw [Category.assoc]; exact Over.w w
  refine ⟨Over.homMk (h.1.lift _ _ hw) (h.1.lift_snd _ _ hw), ?_⟩
  apply Over.OverMorphism.ext
  exact h.1.lift_fst _ _ hw

def tanEquiv (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') : (epsAt y ⟶ G') ≃* (epsAt (y ≫ f) ⟶ G) :=
  { Equiv.ofBijective (tanMap h y) ⟨tanMap_injective h y, tanMap_surjective h y⟩ with
    map_mul' := tanMap_mul h y }

@[simp] theorem tanEquiv_apply (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    tanEquiv h y v = tanMap h y v := rfl

theorem one_left_comp (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') :
    (1 : Over.mk y ⟶ G').left ≫ φ = (1 : Over.mk (y ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (pushAt_one h (Over.mk y))

theorem comp_fst_hom (y : Sp R ⟶ S') :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) ≫ y = y := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext a; rfl
  rw [this]
  simp

theorem isTanAt_iff (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (v : epsAt y ⟶ G') :
    IsTanAt G (y ≫ f) (tanMap h y v) ↔ IsTanAt G' y v := by
  unfold IsTanAt
  rw [← one_left_comp h y, tanMap_left]
  constructor
  · intro e
    refine left_eq_of_comp h ?_ ?_
    · rw [Category.assoc]; exact e
    · have h1 : v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y := Over.w v
      have h2 : (1 : Over.mk y ⟶ G').left ≫ G'.hom = y := Over.w _
      rw [Category.assoc, h1, h2]
      exact comp_fst_hom y
  · intro e
    rw [← Category.assoc, e]

theorem epsMul_comp_algebraMap (c : R) : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  ext a <;> simp [epsMul]

theorem eps_left_iff (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') (c : R) (u v : epsAt y ⟶ G') :
    (tanMap h y u).left = spMap (epsMul c) ≫ (tanMap h y v).left ↔ u.left = spMap (epsMul c) ≫ v.left := by
  rw [tanMap_left, tanMap_left]
  constructor
  · intro e
    refine left_eq_of_comp h ?_ ?_
    · rw [Category.assoc]; exact e
    · have h1 : u.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y := Over.w u
      have h2 : v.left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ y := Over.w v
      rw [Category.assoc, h1, h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        epsMul_comp_algebraMap]
  · intro e
    rw [e, Category.assoc]

theorem isComb_iff (h : IsGrpPullback G' G f φ) (y : Sp R ⟶ S') {n : ℕ} (c : Fin n → R)
    (v : Fin n → (epsAt y ⟶ G')) (w : epsAt y ⟶ G') :
    IsComb c (fun i => tanMap h y (v i)) (tanMap h y w) ↔ IsComb c v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    obtain ⟨u', rfl⟩ : ∃ u' : Fin n → (epsAt y ⟶ G'), u = fun i => tanMap h y (u' i) :=
      ⟨fun i => (tanMap_surjective h y (u i)).choose,
        funext fun i => ((tanMap_surjective h y (u i)).choose_spec).symm⟩
    refine ⟨u', fun i => (eps_left_iff h y _ _ _).1 (hu i), (tanEquiv h y).injective ?_⟩
    have := map_list_prod (tanEquiv h y) (List.ofFn u')
    rw [List.map_ofFn] at this
    rw [this]
    exact hw
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => tanMap h y (u i), fun i => (eps_left_iff h y _ _ _).2 (hu i), ?_⟩
    have := map_list_prod (tanEquiv h y) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact this

variable {O : Type} [CommRing O]

theorem isEigVec_iff (h : IsGrpPullback G' G f φ) (act' : OAct O G') (act : OAct O G)
    (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (y : Sp R ⟶ S') (τ : O →+* R) (v : epsAt y ⟶ G') :
    IsEigVec act (y ≫ f) τ (tanMap h y v) ↔ IsEigVec act' y τ v := by
  have key : ∀ a, tanMap h y v ≫ act.act a = tanMap h y (v ≫ act'.act a) := fun a => by
    apply Over.OverMorphism.ext
    change (v.left ≫ φ) ≫ (act.act a).left = (v.left ≫ (act'.act a).left) ≫ φ
    rw [Category.assoc, Category.assoc, hact]
  unfold IsEigVec
  rw [isTanAt_iff]
  refine and_congr_right fun _ => forall_congr' fun a => ?_
  rw [key]
  exact eps_left_iff h y (τ a) _ _

theorem isEigFrame_iff (h : IsGrpPullback G' G f φ) (act' : OAct O G') (act : OAct O G)
    (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (y : Sp R ⟶ S') (τ : O →+* R) {n : ℕ}
    (v : Fin n → (epsAt y ⟶ G')) :
    IsEigFrame act (y ≫ f) τ (fun i => tanMap h y (v i)) ↔ IsEigFrame act' y τ v := by
  unfold IsEigFrame
  refine and_congr (forall_congr' fun i => isEigVec_iff h act' act hact y τ (v i)) ?_
  constructor
  · intro H w hw
    obtain ⟨c, hc, hu⟩ := H (tanMap h y w) ((isEigVec_iff h act' act hact y τ w).2 hw)
    exact ⟨c, (isComb_iff h y c v w).1 hc, fun c' hc' => hu c' ((isComb_iff h y c' v w).2 hc')⟩
  · intro H w hw
    obtain ⟨w', rfl⟩ := tanMap_surjective h y w
    obtain ⟨c, hc, hu⟩ := H w' ((isEigVec_iff h act' act hact y τ w').1 hw)
    exact ⟨c, (isComb_iff h y c v w').2 hc, fun c' hc' => hu c' ((isComb_iff h y c' v w').1 hc')⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

namespace GlobalTheory.CompanionTheory.Ar.LocFn

open Transfer

theorem dualMap_eq_pj {A T : Type} [CommRing A] [CommRing T] (θ : A →+* T) :
    Formalism.L2.Pj.dualMap θ = GlobalTheory.CompanionTheory.Ar.dualMap θ := by
  apply RingHom.ext
  intro a
  rfl

theorem exists_eigFrame_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : Type) [CommRing T] (y : Sp T ⟶ Xo.XF c) (A : Type) [CommRing A] (x₀ : Sp A ⟶ Y.X) (κ : c.F →+* A) (θ : A →+* T) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt x₀ ⟶ Y.t.G)), spMap θ ≫ x₀ = y ≫ Y.j → StableEig Y.t x₀ κ σ e → ∃ V : Fin r → (epsAt (under y) ⟶ Xo.univ.t.G), (∀ i, Tied Y y (V i).left (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left)) ∧ IsEigFrame Xo.univ.t.act (under y) ((θ.comp κ).comp (tauIn c σ)) V := by
  intro E _ _ _ H D l Xo c O _ β Y T _ y A _ x₀ κ θ σ r e hx hst
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  have hover : ∀ i, (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) ≫ Y.t.G.hom =
      spMap (algebraMap T (DualNumber T)) ≫ y ≫ Y.j := fun i => by
    have h1 : (e i).left ≫ Y.t.G.hom = spMap (algebraMap A (DualNumber A)) ≫ x₀ := Over.w (e i)
    rw [Category.assoc, h1, ← hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    have : (GlobalTheory.CompanionTheory.Ar.dualMap θ).comp (algebraMap A (DualNumber A)) = (algebraMap T (DualNumber T)).comp θ := by
      have hA : ∀ a : A, algebraMap A (DualNumber A) a = TrivSqZeroExt.inl a := fun _ => rfl
      have hT : ∀ a : T, algebraMap T (DualNumber T) a = TrivSqZeroExt.inl a := fun _ => rfl
      ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, hA, hT]
    rw [this]
  let v : Fin r → (epsAt (y ≫ Y.j) ⟶ Y.t.G) := fun i => Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) (hover i)
  have hv : IsEigFrame Y.t.act (y ≫ Y.j) ((θ.comp κ).comp (tauIn c σ)) v :=
    hst T θ (y ≫ Y.j) hx v (fun i => rfl)
  let w : Fin r → (epsAt y ⟶ Y.oF.t.G) := fun i => (tanMap_surjective hq y (v i)).choose
  have hw : ∀ i, tanMap hq y (w i) = v i := fun i => (tanMap_surjective hq y (v i)).choose_spec
  have hfr : IsEigFrame Y.oF.t.act y ((θ.comp κ).comp (tauIn c σ)) w := by
    refine (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y _ w).1 ?_
    simpa only [hw] using hv
  refine ⟨fun i => tanMap hp y (w i), fun i => ⟨(w i).left, Over.w (w i), rfl, ?_⟩,
    (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y _ w).2 hfr⟩
  have := congrArg (fun z => z.left) (hw i)
  rw [dualMap_eq_pj]
  exact this

end GlobalTheory.CompanionTheory.Ar.LocFn
