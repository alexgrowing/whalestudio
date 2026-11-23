import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (f : G ⟶ G) [IsMonHom f] : IsTan (w ≫ f) := by
  unfold IsTan at hw ⊢
  rw [← Category.assoc, hw]
  first
  | simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]
  | simp [Hom.one_def]

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def tvec (c : Fin n → R) : sp (R₀ := R) (DualNumber R) ⟶ G := spMap (dualLift c) ≫ x 1

include hx in
theorem isTan_tvec (c : Fin n → R) : IsTan (tvec (x := x) c) := isTan_dualLift hx c

private lemma sp_tangent_ext {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (hw' : IsTan w')
    (h : tcoord hx w hw = tcoord hx w' hw') : w = w' := by
  calc w = spMap (dualLift (tcoord hx w hw)) ≫ x 1 := tcoord_spec hx w hw
    _ = spMap (dualLift (tcoord hx w' hw')) ≫ x 1 := by rw [h]
    _ = w' := (tcoord_spec hx w' hw').symm

theorem tcoord_tvec (c : Fin n → R) : tcoord hx (tvec (x := x) c) (isTan_tvec hx c) = c :=
  (exists_coord hx (tvec (x := x) c) (isTan_tvec hx c)).unique (tcoord_spec hx _ _) rfl

include hx in
theorem tvec_add (c c' : Fin n → R) : tvec (x := x) (c + c') = tvec (x := x) c * tvec (x := x) c' := by
  refine sp_tangent_ext hx (isTan_tvec hx (c + c')) (isTan_mul (isTan_tvec hx c) (isTan_tvec hx c')) ?_
  rw [tcoord_mul hx (isTan_tvec hx c) (isTan_tvec hx c'), tcoord_tvec, tcoord_tvec, tcoord_tvec]

include hx in
theorem tvec_smul (a : R) (c : Fin n → R) : tvec (x := x) (a • c) = spMap (scaleD a) ≫ tvec (x := x) c := by
  refine sp_tangent_ext hx (isTan_tvec hx (a • c)) (isTan_scale a (isTan_tvec hx c)) ?_
  rw [tcoord_scale hx a (isTan_tvec hx c), tcoord_tvec, tcoord_tvec]

theorem tcoord_congr {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (h : w = w') (hw : IsTan w) (hw' : IsTan w') :
    tcoord hx w hw = tcoord hx w' hw' := by
  subst h
  rfl

def tmap (f : G ⟶ G) [IsMonHom f] : (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun c := tcoord hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)
  map_add' c c' := by
    have e : tvec (x := x) (c + c') ≫ f = (tvec (x := x) c ≫ f) * (tvec (x := x) c' ≫ f) := by
      rw [tvec_add hx, Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
    show tcoord hx _ _ = tcoord hx _ _ + tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_mul (isTan_comp (isTan_tvec hx c) f) (isTan_comp (isTan_tvec hx c') f)),
      tcoord_mul hx]
  map_smul' a c := by
    have e : tvec (x := x) (a • c) ≫ f = spMap (scaleD a) ≫ (tvec (x := x) c ≫ f) := by
      rw [tvec_smul hx, Category.assoc]
    show tcoord hx _ _ = a • tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_scale a (isTan_comp (isTan_tvec hx c) f)), tcoord_scale hx]

theorem tvec_tmap (f : G ⟶ G) [IsMonHom f] (c : Fin n → R) : tvec (x := x) (tmap hx f c) = tvec (x := x) c ≫ f :=
  (tcoord_spec hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)).symm

end ReciprocityTheory.ChartRestriction.G.Chart
