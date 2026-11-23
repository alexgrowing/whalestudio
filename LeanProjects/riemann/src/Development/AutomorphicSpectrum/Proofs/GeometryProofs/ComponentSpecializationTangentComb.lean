import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem grpPull_mul (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f)
    (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact hφ.2 T x y x₀ y₀ hx hy

theorem grpPull_one (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (1 : T ⟶ G'))
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have h := hφ.2 T 1 1 e e rfl rfl
  rw [_root_.mul_one] at h
  have h2 : e * e = e := Over.OverMorphism.ext h
  have h3 : e = 1 := mul_eq_left.1 h2
  exact (congrArg (fun q : Over.mk (T.hom ≫ f) ⟶ G => q.left) h3).symm

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Same

variable {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}

theorem sameVec_one (Y : Model Xo c β) (y : Sp F ⟶ Xo.XF c) : SameVec Y y 1 1 := by
  let T : Over (Xo.XF c) := epsAt y
  refine ⟨(1 : T ⟶ Y.oF.t.G).left, Over.w _, ?_, ?_⟩
  · exact (grpPull_one Y.m0.cart T (Category.assoc _ _ _).symm).symm
  · exact (grpPull_one Y.m.cart T (Category.assoc _ _ _).symm).symm

theorem sameVec_mul {a b : epsAt (under y) ⟶ Xo.univ.t.G} {a' b' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y a a') (h₂ : SameVec Y y b b') : SameVec Y y (a * b) (a' * b') := by
  obtain ⟨u₁, p₁, q₁, r₁⟩ := h₁
  obtain ⟨u₂, p₂, q₂, r₂⟩ := h₂
  let T : Over (Xo.XF c) := epsAt y
  let x₁ : T ⟶ Y.oF.t.G := Over.homMk u₁ p₁
  let x₂ : T ⟶ Y.oF.t.G := Over.homMk u₂ p₂
  refine ⟨(x₁ * x₂).left, Over.w (x₁ * x₂), ?_, ?_⟩
  · exact (grpPull_mul Y.m0.cart T (Category.assoc _ _ _).symm x₁ x₂ a b q₁.symm q₂.symm).symm
  · exact (grpPull_mul Y.m.cart T (Category.assoc _ _ _).symm x₁ x₂ a' b' r₁.symm r₂.symm).symm

theorem sameVec_scale {a u : epsAt (under y) ⟶ Xo.univ.t.G} {a' : epsAt (y ≫ Y.j) ⟶ Y.t.G} (h : SameVec Y y a a')
    (r : F) (hu : u.left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ a.left) :
    SameVec Y y u (LieTangent.epsScale (y ≫ Y.j) r ≫ a') := by
  obtain ⟨u₀, p, q, t⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ u₀, ?_, ?_, ?_⟩
  · rw [Category.assoc, p, ← Category.assoc, LieTangent.spec_eps_alg]
  · rw [Category.assoc, q, hu]
  · rw [Category.assoc, t]
    rfl

end Same

theorem valFam_sum {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hg : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) {n : ℕ} (e : Fin n → Z.V)
    (u : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G))
    (h : ∀ j, ∃ a, Z.M.ValAt (y ≫ Y.j) (e j) a ∧ SameVec Y y (u j) a) :
    ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, e j) w' ∧ SameVec Y y (List.ofFn u).prod w' := by
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa using Z.M.valAt_zero hg
    · simpa using sameVec_one Y y
  | succ n ih =>
    obtain ⟨a, ha, hb⟩ := h 0
    obtain ⟨w', hw, hs⟩ := ih (fun i => e i.succ) (fun i => u i.succ) fun i => h i.succ
    refine ⟨a * w', ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      exact ha.add hw
    · rw [List.ofFn_succ, List.prod_cons]
      exact sameVec_mul hb hs

theorem valFam_sum_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ y n b v s r w hg h hs hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine valFam_sum Z y hg _ u fun j => ?_
  obtain ⟨h1, t, e1, e2⟩ := hs j
  obtain ⟨a, ha, hb⟩ := h j
  have h2 := ha.smul h1 t
  rw [e1, e2] at h2
  exact ⟨_, h2, sameVec_scale hb (r j) (hu j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
