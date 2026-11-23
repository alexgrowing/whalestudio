import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DivConst

theorem gs_const {R K : Type} [CommRing R] [CommRing K] (g : R →+* K) {X Y : Scheme.{0}} {q : X ⟶ Sp R}
    {p : Y ⟶ Sp K} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (y : Y) (b : R) :
    gs φ y ⊤ (q.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) =
      gs p y ⊤ ((Scheme.ΓSpecIso (.of K)).inv.hom (g b)) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp R ↦ φ.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) w
  have h₂ := congrArg (fun φ : CommRingCat.of R ⟶ Γ(Spec (.of K), ⊤) ↦ φ.hom b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [gs_eq φ y ⊤ trivial, gs_eq p y ⊤ trivial]
  exact congrArg (Y.presheaf.germ ⊤ y trivial).hom (h₁.trans (congrArg p.appTop.hom h₂.symm))

theorem exists_genPull_eq : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  intro R K _ _ _ X Y φ p w M c a b hab u hu H
  let β : Γ(X.left, ⊤)ˣ := Units.map (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toMonoidHom b
  refine ⟨⟨fun i => u.s i * (res le_top β)⁻¹⟩, fun i j => unit_ext fun x hx => ?_, ?_⟩
  · have e := congrArg (gm (𝟙 X.left) x (M.U i ⊓ M.U j)) (hu i j)
    simp only [map_mul, map_inv] at e ⊢
    rw [e, gm_res _ x _ hx (res le_top β), gm_res _ x _ hx (res le_top β), gm_res _ x _ hx.1 β,
      gm_res _ x _ hx.2 β, mul_assoc]
  · obtain ⟨s⟩ := c
    refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
    have hy' : φ y ∈ M.U (j PUnit.unit) := mem_pull.1 hy
    refine (gm_res _ y _ hy _).trans ((gm_pull (𝟙 Y) φ y _ hy' _).trans ?_)
    have e := H (j PUnit.unit) Y (𝟙 Y) y hy'
    have e' : (gm (𝟙 Y ≫ φ) y ⊤ β).val = gs (𝟙 Y ≫ p) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
      rw [← gs_unit _ y ⊤ trivial, ← hab, Category.id_comp, Category.id_comp]
      exact gs_const _ w y b
    rw [← e', ← Units.val_mul] at e
    rw [map_mul, map_inv, gm_res (𝟙 Y ≫ φ) y _ hy' β, Units.ext e, mul_inv_cancel_comm]
    rfl

end GlobalTheory.DivConst
