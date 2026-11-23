import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompOfCechPt

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial

namespace UpperTheory.Gal.KunnethLefschetz.G

section Pts
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

theorem exists_pts {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ Y), ∃ x h, z = cechPt f k x y h := by
  let φ : yoneda.obj U ⟶ (cech f) _⦋k⦌ := yonedaEquiv.symm z
  refine ⟨fun i => Yoneda.fullyFaithful.preimage (φ ≫ WidePullback.π _ i),
    Yoneda.fullyFaithful.preimage (φ ≫ WidePullback.base _), fun i => ?_, ?_⟩
  · apply Yoneda.fullyFaithful.map_injective
    simp
  · have e : φ = WidePullback.lift (yoneda.map (Yoneda.fullyFaithful.preimage (φ ≫ WidePullback.base _)))
        (fun i => yoneda.map (Yoneda.fullyFaithful.preimage (φ ≫ WidePullback.π _ i))) (by simp) := by
      apply WidePullback.hom_ext <;> simp
    have hz : z = yonedaEquiv φ := by simp [φ]
    refine hz.trans ?_
    conv_lhs => rw [e]
    rfl

def pts {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) : Fin (k + 1) → (U ⟶ Y) :=
  (exists_pts f z).choose

theorem pts_spec {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) :
    ∃ x h, z = cechPt f k x (pts f z) h := (exists_pts f z).choose_spec

private theorem widePullback_pi_app_cechPt_eq {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y))
    (h : ∀ i, y i ≫ f = x) (i : Fin (k + 1)) :
    ((WidePullback.π (fun _ : Fin (k + 1) => (Arrow.mk (yoneda.map f)).hom) i).app (op U)) (cechPt f k x y h) = y i := by
  change ((WidePullback.π (fun _ : Fin (k + 1) => (Arrow.mk (yoneda.map f)).hom) i).app (op U))
    (yonedaEquiv (WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i)) _)) = y i
  rw [← yonedaEquiv_comp]
  simp only [WidePullback.lift_π]
  rw [yonedaEquiv_apply]
  exact Category.id_comp (y i)

private theorem pts_eq_widePullback_pi_app {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    pts f z i = ((WidePullback.π (fun _ : Fin (k + 1) => (Arrow.mk (yoneda.map f)).hom) i).app (op U)) z := by
  obtain ⟨x, h, e⟩ := pts_spec f z
  conv_rhs => rw [e]
  rw [widePullback_pi_app_cechPt_eq]

theorem pts_eq {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i j : Fin (k + 1)) :
    pts f z i ≫ f = pts f z j ≫ f := by
  obtain ⟨x, h, -⟩ := pts_spec f z
  exact (h i).trans (h j).symm

theorem pts_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y))
    (h : ∀ i, y i ≫ f = x) : pts f (cechPt f k x y h) = y := by
  funext i
  rw [pts_eq_widePullback_pi_app, widePullback_pi_app_cechPt_eq]

theorem pts_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    pts f (Sx.res g z) i = g ≫ pts f z i := by
  rw [pts_eq_widePullback_pi_app, pts_eq_widePullback_pi_app]
  exact NatTrans.naturality_apply (WidePullback.π (fun _ : Fin (k + 1) => (Arrow.mk (yoneda.map f)).hom) i) g.op z

theorem pts_along {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts f (Sx.along z θ) i = pts f z (θ.toOrderHom i) := by
  rw [pts_eq_widePullback_pi_app, pts_eq_widePullback_pi_app]
  have e : (cech f).map θ.op ≫ WidePullback.π (fun _ ↦ (Arrow.mk (yoneda.map f)).hom) i =
      WidePullback.π (fun _ ↦ (Arrow.mk (yoneda.map f)).hom) (θ.toOrderHom i) := by
    simp [cech, Arrow.cechNerve]
  exact congrArg (fun φ : (cech f) _⦋k⦌ ⟶ _ => ConcreteCategory.hom (φ.app (op U)) z) e

theorem pts_inj {k : ℕ} {U : Scheme.{0}} {z z' : Sx (cech f) k U} (e : pts f z = pts f z') : z = z' := by
  obtain ⟨x, h, hz⟩ := pts_spec f z
  obtain ⟨x', h', hz'⟩ := pts_spec f z'
  have hx : x = x' := (h 0).symm.trans ((congrArg (· ≫ f) (congrFun e 0)).trans (h' 0))
  subst hx
  have key : ∀ (a b : Fin (k + 1) → (U ⟶ Y)) (ha : ∀ i, a i ≫ f = x) (hb : ∀ i, b i ≫ f = x),
      a = b → cechPt f k x a ha = cechPt f k x b hb := by
    rintro a b ha hb rfl
    rfl
  exact hz.trans ((key _ _ _ _ e).trans hz'.symm)

end Pts

theorem Um.unit_unique {A : Type} [CommRing A] {N : ℕ} (v : Um N A) {u u' : Aˣ}
    (h : (u : A) • v.1 = (u' : A) • v.1) : u = u' := by
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1
    (show (1 : A) ∈ Ideal.span (Set.range v.1) by rw [v.2]; trivial)
  apply Units.ext
  have hi : ∀ i, (u : A) * v.1 i = (u' : A) * v.1 i := fun i => by simpa using congrFun h i
  calc (u : A) = u * ∑ i, c i * v.1 i := by rw [hc, mul_one]
    _ = ∑ i, c i * (u * v.1 i) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, c i * (u' * v.1 i) := by simp only [hi]
    _ = u' * ∑ i, c i * v.1 i := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = u' := by rw [hc, mul_one]

theorem Um.hom_heq {A : Type} [CommRing A] {N : ℕ} {v v' w w' : Um N A} (hv : v = v') (hw : w = w') (p : v ⟶ w) (p' : v' ⟶ w')
    (h : p.1 = p'.1) : HEq p p' := by
  subst hv hw
  exact heq_of_eq (Subtype.ext h)

namespace PBData
variable {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d)

theorem g_self {V : Scheme.{0}} (a : V ⟶ P.W') (h : a ≫ P.c = a ≫ P.c) : P.g a a h = 1 :=
  mul_eq_left.mp (P.g_coc a a a h h)

theorem g_congr {V : Scheme.{0}} {a a' b b' : V ⟶ P.W'} (ha : a = a') (hb : b = b')
    (h : a ≫ P.c = b ≫ P.c) (h' : a' ≫ P.c = b' ≫ P.c) : P.g a b h = P.g a' b' h' := by
  subst ha hb; rfl

theorem w_congr {V : Scheme.{0}} {a a' b b' : V ⟶ P.T'} (ha : a = a') (hb : b = b')
    (h : a ≫ P.e = b ≫ P.e) (h' : a' ≫ P.e = b' ≫ P.e) : P.w a b h = P.w a' b' h' := by
  subst ha hb; rfl

theorem ρ_eq {V : Scheme.{0}} {a b : V ⟶ P.T'} (h : a ≫ P.e = b ≫ P.e) :
    (a ≫ P.ρ) ≫ P.c = (b ≫ P.ρ) ≫ P.c := by
  simp only [Category.assoc, P.comm]
  simp only [← Category.assoc, h]

def gFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ P.W')) (hy : ∀ i j, y i ≫ P.c = y j ≫ P.c) :
    ComposableArrows (SingleObj (GL (Fin d) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := P.g (y i) (y j) (hy i j)
  map_id i := P.g_self _ _
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    exact (P.g_coc _ _ _ _ _).symm

theorem gFun_res {U V : Scheme.{0}} {k : ℕ} (s : V ⟶ U) (y : Fin (k + 1) → (U ⟶ P.W'))
    (hy : ∀ i j, y i ≫ P.c = y j ≫ P.c) (y' : Fin (k + 1) → (V ⟶ P.W'))
    (hy' : ∀ i j, y' i ≫ P.c = y' j ≫ P.c) (e : ∀ i, y' i = s ≫ y i) :
    P.gFun y' hy' = (show Fin (k + 1) ⥤ (glCat d).obj Γ(U, ⊤) from P.gFun y hy) ⋙
      ((glCat d).map (Scheme.Γ.map s.op)).toFunctor := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
  have hs : (s ≫ y i) ≫ P.c = (s ≫ y j) ≫ P.c := by simp only [Category.assoc, hy i j]
  exact (P.g_congr (e i) (e j) _ hs).trans (P.g_nat s (y i) (y j) (hy i j))

def bunV : cech P.c ⟶ ofCat (glCat d) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        P.gFun (pts P.c (show Sx (cech P.c) n.unop.len U.unop from z)) (pts_eq P.c _)
      naturality := fun U U' s => by
        ext z
        exact P.gFun_res s.unop _ (pts_eq P.c _) _ (pts_eq P.c _) (fun i => pts_res P.c s.unop _ i) }
  naturality n m θ := by
    ext U z
    change P.gFun (pts P.c (Sx.along (show Sx (cech P.c) n.unop.len U.unop from z) θ.unop)) (pts_eq P.c _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ P.gFun (pts P.c (show Sx (cech P.c) n.unop.len U.unop from z)) (pts_eq P.c _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact P.g_congr (pts_along P.c _ θ.unop i) (pts_along P.c _ θ.unop j) _ _

theorem w_self {V : Scheme.{0}} (a : V ⟶ P.T') (h : a ≫ P.e = a ≫ P.e) : P.w a a h = 1 := by
  have e := P.gv a a h (P.ρ_eq h)
  rw [P.g_self] at e
  refine Um.unit_unique (P.v a) ?_
  simpa using e.symm

theorem w_coc {V : Scheme.{0}} (a b k : V ⟶ P.T') (h : a ≫ P.e = b ≫ P.e) (h' : b ≫ P.e = k ≫ P.e) :
    P.w b k h' * P.w a b h = P.w a k (h.trans h') := by
  apply Um.unit_unique (P.v k)
  have h1 := P.gv a b h (P.ρ_eq h)
  have h2 := P.gv b k h' (P.ρ_eq h')
  have h3 := P.gv a k (h.trans h') (P.ρ_eq (h.trans h'))
  have hc := P.g_coc (a ≫ P.ρ) (b ≫ P.ρ) (k ≫ P.ρ) (P.ρ_eq h) (P.ρ_eq h')
  rw [← h3, ← hc]
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, smul_smul]
  rw [mul_comm]

private theorem gl_map_mulVec_comp_eq_comp_mulVec {n : ℕ} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (M : GL (Fin n) A)
    (x : Fin n → A) :
    (↑(Matrix.GeneralLinearGroup.map φ M) : Matrix (Fin n) (Fin n) B).mulVec (φ ∘ x) =
      φ ∘ (↑M : Matrix (Fin n) (Fin n) A).mulVec x := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem w_nat {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ P.T') (h : a ≫ P.e = b ≫ P.e)
    (h' : (s ≫ a) ≫ P.e = (s ≫ b) ≫ P.e) :
    P.w (s ≫ a) (s ≫ b) h' = Units.map s.appTop.hom.toMonoidHom (P.w a b h) := by
  apply Um.unit_unique (P.v (s ≫ b))
  have hs : (s ≫ a ≫ P.ρ) ≫ P.c = (s ≫ b ≫ P.ρ) ≫ P.c := by
    simpa only [Category.assoc] using congrArg (s ≫ ·) (P.ρ_eq h)
  have hg : P.g ((s ≫ a) ≫ P.ρ) ((s ≫ b) ≫ P.ρ) (P.ρ_eq h') =
      Matrix.GeneralLinearGroup.map s.appTop.hom (P.g (a ≫ P.ρ) (b ≫ P.ρ) (P.ρ_eq h)) :=
    (P.g_congr (Category.assoc _ _ _) (Category.assoc _ _ _) _ hs).trans (P.g_nat s _ _ _)
  rw [← P.gv (s ≫ a) (s ≫ b) h' (P.ρ_eq h'), hg, P.v_nat s a, P.v_nat s b, gl_map_mulVec_comp_eq_comp_mulVec,
    P.gv a b h (P.ρ_eq h)]
  funext i
  simp

def wFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ P.T')) (hy : ∀ i j, y i ≫ P.e = y j ≫ P.e) :
    ComposableArrows (Um d Γ(V, ⊤)) k where
  obj i := P.v (y i)
  map {i j} _ := ⟨(P.g _ _ (P.ρ_eq (hy i j)), P.w _ _ (hy i j)), P.gv _ _ _ _⟩
  map_id i := Subtype.ext (Prod.ext (P.g_self _ _) (P.w_self _ _))
  map_comp {i j l} _ _ := Subtype.ext (Prod.ext (P.g_coc _ _ _ _ _).symm (P.w_coc _ _ _ _ _).symm)

theorem wFun_res {U V : Scheme.{0}} {k : ℕ} (s : V ⟶ U) (y : Fin (k + 1) → (U ⟶ P.T'))
    (hy : ∀ i j, y i ≫ P.e = y j ≫ P.e) (y' : Fin (k + 1) → (V ⟶ P.T'))
    (hy' : ∀ i j, y' i ≫ P.e = y' j ≫ P.e) (e : ∀ i, y' i = s ≫ y i) :
    P.wFun y' hy' = (show Fin (k + 1) ⥤ (pglCat d).obj Γ(U, ⊤) from P.wFun y hy) ⋙
      ((pglCat d).map (Scheme.Γ.map s.op)).toFunctor := by
  have ho : ∀ i, P.v (y' i) = (Um.map d s.appTop.hom).obj (P.v (y i)) := fun i =>
    Subtype.ext (by rw [e i, P.v_nat]; rfl)
  refine CategoryTheory.Functor.hext ho (fun i j p => Um.hom_heq (ho i) (ho j) _ _ ?_)
  have hs : (s ≫ y i) ≫ P.e = (s ≫ y j) ≫ P.e := by simp only [Category.assoc, hy i j]
  have hsρ : (s ≫ y i ≫ P.ρ) ≫ P.c = (s ≫ y j ≫ P.ρ) ≫ P.c := by
    simpa only [Category.assoc] using congrArg (s ≫ ·) (P.ρ_eq (hy i j))
  refine Prod.ext ?_ ?_
  · exact (P.g_congr (by rw [e i, Category.assoc]) (by rw [e j, Category.assoc]) _ hsρ).trans
      (P.g_nat s _ _ _)
  · exact (P.w_congr (e i) (e j) _ hs).trans (P.w_nat s _ _ _ _)

def bunP : cech P.e ⟶ PGL d where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        P.wFun (pts P.e (show Sx (cech P.e) n.unop.len U.unop from z)) (fun i j => pts_eq P.e _ i j)
      naturality := fun U U' s => by
        ext z
        exact P.wFun_res s.unop _ (pts_eq P.e _) _ (pts_eq P.e _) (fun i => pts_res P.e s.unop _ i) }
  naturality n m θ := by
    ext U z
    change P.wFun (pts P.e (Sx.along (show Sx (cech P.e) n.unop.len U.unop from z) θ.unop)) (pts_eq P.e _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ P.wFun (pts P.e (show Sx (cech P.e) n.unop.len U.unop from z)) (pts_eq P.e _)
    refine CategoryTheory.Functor.hext (fun i => congrArg P.v (pts_along P.e _ θ.unop i)) (fun i j p => Um.hom_heq
      (congrArg P.v (pts_along P.e _ θ.unop i)) (congrArg P.v (pts_along P.e _ θ.unop j)) _ _ ?_)
    exact Prod.ext (P.g_congr (congrArg (· ≫ P.ρ) (pts_along P.e _ θ.unop i)) (congrArg (· ≫ P.ρ) (pts_along P.e _ θ.unop j)) _ _)
      (P.w_congr (pts_along P.e _ θ.unop i) (pts_along P.e _ θ.unop j) _ _)

def ρmap : cech P.e ⟶ cech P.c :=
  SimplicialObject.cechNerve.map (Arrow.homMk (yoneda.map P.ρ) (yoneda.map r)
    (show yoneda.map P.ρ ≫ yoneda.map P.c = yoneda.map P.e ≫ yoneda.map r by
      rw [← yoneda.map_comp, ← yoneda.map_comp, P.comm]) : Arrow.mk (yoneda.map P.e) ⟶ Arrow.mk (yoneda.map P.c))

theorem ρmap_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ T) (y : Fin (k + 1) → (U ⟶ P.T')) (h : ∀ i, y i ≫ P.e = x) :
    Sx.map P.ρmap (cechPt P.e k x y h) =
      cechPt P.c k (x ≫ r) (fun i => y i ≫ P.ρ) (fun i => by rw [Category.assoc, P.comm, ← Category.assoc, h]) := by
  have key : WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by simp [← Functor.map_comp, h]) ≫ P.ρmap.app (op ⦋k⦌) =
      WidePullback.lift (objs := fun _ : Fin (k + 1) => (Arrow.mk (yoneda.map P.c)).left)
        (arrows := fun _ => (Arrow.mk (yoneda.map P.c)).hom) (yoneda.map (x ≫ r))
        (fun i => yoneda.map (y i ≫ P.ρ))
        (fun i => by simp [← Functor.map_comp, Category.assoc, P.comm, ← h i]) := by
    apply WidePullback.hom_ext <;> simp [ρmap]
  exact congrArg (fun φ : yoneda.obj U ⟶ (cech P.c) _⦋k⦌ => ConcreteCategory.hom (φ.app (op U)) (𝟙 U)) key

theorem pts_ρmap {k : ℕ} {U : Scheme.{0}} (z : Sx (cech P.e) k U) (i : Fin (k + 1)) :
    pts P.c (Sx.map P.ρmap z) i = pts P.e z i ≫ P.ρ := by
  obtain ⟨x, h, e⟩ := pts_spec P.e z
  conv_lhs => rw [e]
  rw [ρmap_cechPt, pts_cechPt]

theorem ρmap_comm : P.ρmap ≫ P.bunV = P.bunP ≫ PGL.pr d := by
  ext n U z
  change P.gFun (pts P.c (Sx.map P.ρmap (show Sx (cech P.e) n.unop.len U.unop from z))) (pts_eq P.c _) =
    (show Fin (n.unop.len + 1) ⥤ Um d Γ(U.unop, ⊤) from P.wFun (pts P.e (show Sx (cech P.e) n.unop.len U.unop from z)) (pts_eq P.e _)) ⋙ Um.toGL d _
  refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
  exact P.g_congr (pts_ρmap P _ i) (pts_ρmap P _ j) _ _

def bunF : cech P.e ⟶ pullback P.bunV (PGL.pr d) := pullback.lift P.ρmap P.bunP P.ρmap_comm

def PA : PSh where
  obj U := (U.unop ⟶ P.W') × Um d Γ(U.unop, ⊤)
  map s := TypeCat.ofHom fun p => (s.unop ≫ p.1, (Um.map d s.unop.appTop.hom).obj p.2)
  map_id U := by
    ext p
    · exact Category.id_comp _
    · simp [Um.map]
  map_comp s s' := by
    ext p
    · simp
    · simp [Um.map]
      rfl

def rel (U : Scheme.{0}) (p p' : P.PA.obj (op U)) : Prop :=
  ∃ (h : p.1 ≫ P.c = p'.1 ≫ P.c) (u : (Γ(U, ⊤))ˣ), (P.g p.1 p'.1 h).1.mulVec p.2.1 = (u : Γ(U, ⊤)) • p'.2.1

theorem rel_refl (U : Scheme.{0}) (p : P.PA.obj (op U)) : P.rel U p p :=
  ⟨rfl, 1, by rw [P.g_self]; simp⟩

theorem rel_symm {U : Scheme.{0}} {p p' : P.PA.obj (op U)} : P.rel U p p' → P.rel U p' p := by
  rintro ⟨h, u, e⟩
  refine ⟨h.symm, u⁻¹, ?_⟩
  have e1 : P.g p'.1 p.1 h.symm * P.g p.1 p'.1 h = 1 := by rw [P.g_coc, P.g_self]
  have e2 : (P.g p'.1 p.1 h.symm).1.mulVec ((P.g p.1 p'.1 h).1.mulVec p.2.1) = p.2.1 := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e1]; simp
  rw [e, Matrix.mulVec_smul] at e2
  rw [← e2, smul_smul]
  simp

theorem rel_trans {U : Scheme.{0}} {p p' p'' : P.PA.obj (op U)} : P.rel U p p' → P.rel U p' p'' → P.rel U p p'' := by
  rintro ⟨h, u, e⟩ ⟨h', u', e'⟩
  refine ⟨h.trans h', u' * u, ?_⟩
  rw [← P.g_coc _ _ _ h h', Units.val_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, e', smul_smul, Units.val_mul, mul_comm]

theorem rel_res {U V : Scheme.{0}} (s : V ⟶ U) {p p' : P.PA.obj (op U)} (hp : P.rel U p p') :
    P.rel V (P.PA.map s.op p) (P.PA.map s.op p') := by
  obtain ⟨h, u, hu⟩ := hp
  have hs : (s ≫ p.1) ≫ P.c = (s ≫ p'.1) ≫ P.c := by simp only [Category.assoc, h]
  refine ⟨hs, Units.map s.appTop.hom.toMonoidHom u, ?_⟩
  change (↑(P.g (s ≫ p.1) (s ≫ p'.1) hs) : Matrix (Fin d) (Fin d) Γ(V, ⊤)).mulVec (s.appTop.hom ∘ p.2.1) =
    _ • (s.appTop.hom ∘ p'.2.1)
  rw [P.g_nat s _ _ h, gl_map_mulVec_comp_eq_comp_mulVec, hu]
  funext i
  simp

def relS (U : Scheme.{0}) : Setoid (P.PA.obj (op U)) := ⟨P.rel U, ⟨P.rel_refl U, P.rel_symm, P.rel_trans⟩⟩

def Q : PSh where
  obj U := Quotient (P.relS U.unop)
  map s := TypeCat.ofHom (Quotient.map (sa := P.relS _) (sb := P.relS _) (P.PA.map s) fun _ _ h => P.rel_res s.unop h)
  map_id U := by
    ext x
    induction x using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (congrFun (congrArg (fun f => f.hom) (P.PA.map_id U)) p)
  map_comp s s' := by
    ext x
    induction x using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (congrFun (congrArg (fun f => f.hom) (P.PA.map_comp s s')) p)

abbrev S : Spc := pullback P.bunV (PGL.pr d)

theorem map_res {E E' : Spc} (f : E ⟶ E') {n : ℕ} {U V : Scheme.{0}} (s : V ⟶ U) (z : Sx E n U) :
    Sx.map f (Sx.res s z) = Sx.res s (Sx.map f z) := by
  exact NatTrans.naturality_apply (f.app (op ⦋n⦌)) s.op z

theorem map_along {E E' : Spc} (f : E ⟶ E') {n p : ℕ} {U : Scheme.{0}} (z : Sx E n U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk n) : Sx.map f (Sx.along z θ) = Sx.along (Sx.map f z) θ := by
  exact congrArg (fun φ : E _⦋n⦌ ⟶ E' _⦋p⦌ => ConcreteCategory.hom (φ.app (op U)) z) (f.naturality θ.op)

def sv {n : ℕ} {U : Scheme.{0}} (z : Sx P.S n U) (i : Fin (n + 1)) : P.PA.obj (op U) :=
  (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i,
    (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i)

theorem S_comm {n : ℕ} {U : Scheme.{0}} (z : Sx P.S n U) :
    Sx.map P.bunV (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) =
      Sx.map (PGL.pr d) (Sx.map (pullback.snd P.bunV (PGL.pr d)) z) := by
  exact congrArg (fun φ : P.S ⟶ ofCat (glCat d) => Sx.map φ z) pullback.condition

theorem sv_rel_le {n : ℕ} {U : Scheme.{0}} (z : Sx P.S n U) {i j : Fin (n + 1)} (hij : i ≤ j) :
    P.rel U (P.sv z i) (P.sv z j) := by
  refine ⟨pts_eq P.c _ i j, ((show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from
    Sx.map (pullback.snd P.bunV (PGL.pr d)) z).map (homOfLE hij)).1.2, ?_⟩
  have hg := congrArg (fun F : Fin (n + 1) ⥤ (glCat d).obj Γ(U, ⊤) => F.map (homOfLE hij)) (P.S_comm z)
  have hp := ((show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from
    Sx.map (pullback.snd P.bunV (PGL.pr d)) z).map (homOfLE hij)).2
  convert hp using 3
  all_goals first
    | exact hg
    | rfl

theorem sv_rel {n : ℕ} {U : Scheme.{0}} (z : Sx P.S n U) (i j : Fin (n + 1)) : P.rel U (P.sv z i) (P.sv z j) := by
  rcases le_total i j with h | h
  · exact P.sv_rel_le z h
  · exact P.rel_symm (P.sv_rel_le z h)

theorem sv_res {n : ℕ} {U V : Scheme.{0}} (s : V ⟶ U) (z : Sx P.S n U) (i : Fin (n + 1)) :
    P.sv (Sx.res s z) i = P.PA.map s.op (P.sv z i) := by
  refine Prod.ext ?_ ?_
  · change pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) (Sx.res s z)) i =
      s ≫ pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i
    rw [map_res, pts_res]
  · change (show Fin (n + 1) ⥤ Um d Γ(V, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) (Sx.res s z)).obj i = _
    rw [map_res]
    rfl

theorem sv_along {n p : ℕ} {U : Scheme.{0}} (z : Sx P.S n U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (i : Fin (p + 1)) : P.sv (Sx.along z θ) i = P.sv z (θ.toOrderHom i) := by
  refine Prod.ext ?_ ?_
  · change pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) (Sx.along z θ)) i =
      pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) (θ.toOrderHom i)
    rw [map_along, pts_along]
  · change (show Fin (p + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) (Sx.along z θ)).obj i = _
    rw [map_along]
    rfl

def pS : P.S ⟶ disc.obj P.Q where
  app n :=
    { app := fun U => TypeCat.ofHom fun z => Quotient.mk (P.relS U.unop) (P.sv (show Sx P.S n.unop.len U.unop from z) 0)
      naturality := fun U U' s => by
        ext z
        exact congrArg (Quotient.mk (P.relS U'.unop)) (P.sv_res s.unop _ 0) }
  naturality n m θ := by
    ext U z
    refine Eq.trans (congrArg (Quotient.mk (P.relS U.unop)) (P.sv_along _ θ.unop 0)) (Quotient.sound (s := P.relS U.unop) (P.sv_rel _ _ _))

theorem bunF_fst : P.bunF ≫ pullback.fst P.bunV (PGL.pr d) = P.ρmap := pullback.lift_fst _ _ _

theorem bunF_snd : P.bunF ≫ pullback.snd P.bunV (PGL.pr d) = P.bunP := pullback.lift_snd _ _ _

theorem ρmap_aug : P.ρmap ≫ cechAug P.c = cechAug P.e ≫ sch.map r := by
  ext n : 1
  simp [ρmap, cechAug, sch, Arrow.augmentedCechNerve]

theorem sv_bunF {n : ℕ} {U : Scheme.{0}} (z : Sx (cech P.e) n U) (i : Fin (n + 1)) :
    P.sv (Sx.map P.bunF z) i = (pts P.e z i ≫ P.ρ, P.v (pts P.e z i)) := by
  refine Prod.ext ?_ ?_
  · change pts P.c (Sx.map (P.bunF ≫ pullback.fst P.bunV (PGL.pr d)) z) i = _
    rw [P.bunF_fst, P.pts_ρmap]
  · change (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (P.bunF ≫ pullback.snd P.bunV (PGL.pr d)) z).obj i = _
    rw [P.bunF_snd]
    rfl

theorem lineUnit_bunF {V : Scheme.{0}} (x : V ⟶ T) (a : Fin 2 → (V ⟶ P.T')) (h : ∀ s, a s ≫ P.e = x) :
    lineUnit (P.bunF ≫ pullback.snd P.bunV (PGL.pr d) ≫ PGL.line d) (cechPt P.e 1 x a h) =
      P.w (a 0) (a 1) ((h 0).trans (h 1).symm) := by
  have hb : P.bunF ≫ pullback.snd P.bunV (PGL.pr d) ≫ PGL.line d = P.bunP ≫ PGL.line d := by
    rw [← Category.assoc, P.bunF_snd]
  rw [hb]
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (P.w (pts P.e (cechPt P.e 1 x a h) 0) (pts P.e (cechPt P.e 1 x a h) 1) (pts_eq P.e _ 0 1))) = _
  rw [P.w_congr (congrFun (pts_cechPt P.e x a h) 0) (congrFun (pts_cechPt P.e x a h) 1) _
    ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.det_fin_one]

end PBData
end UpperTheory.Gal.KunnethLefschetz.G
