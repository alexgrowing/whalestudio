import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

private lemma res_res_eq_res_trans {X : Scheme.{0}} {U W Z : X.Opens} (h : W ≤ U) (h' : Z ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma pullU_res_eq_res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) :
    pullU f W (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

private lemma res_pullU_res_eq_res_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (k : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res k (pullU f W (res h x)) = res (k.trans fun _ hy ↦ h hy) (pullU f U x) := by
  rw [pullU_res_eq_res_pullU, res_res_eq_res_trans]

theorem isFrame_pull (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ)
    (Z : Scheme.{0}) (φ : Z ⟶ X) (C' : Type) [Category.{0} C'] (V' : C' → Z.Opens)
    (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ φ ⁻¹ᵁ V (H.obj T)) :
    IsFrame L V hV u → IsFrame (L.pull φ) V' hV' fun T T' a ↦ res (hH T') (pullU φ _ (u _ _ (H.map a))) := by
  rintro ⟨τ, hgen, hcomp⟩
  have hle : ∀ (T : C') (j : PUnit → L.ι), V' T ⊓ (L.pull φ).U j ≤ φ ⁻¹ᵁ (V (H.obj T) ⊓ L.U (j PUnit.unit)) :=
    fun T j x hx ↦ ⟨hH T hx.1, LB.wchart_le L (fun _ ↦ φ) j PUnit.unit hx.2⟩
  refine ⟨fun T j ↦ res (hle T j) (pullU φ _ (τ (H.obj T) (j PUnit.unit))), fun T j j' ↦ ?_, fun T T' a j ↦ ?_⟩
  · have e := congrArg (fun x ↦ res (fun y hy ↦ ⟨⟨hH T hy.1.1, LB.wchart_le L (fun _ ↦ φ) j PUnit.unit hy.1.2⟩,
        LB.wchart_le L (fun _ ↦ φ) j' PUnit.unit hy.2⟩ : V' T ⊓ (L.pull φ).U j ⊓ (L.pull φ).U j' ≤
          φ ⁻¹ᵁ (V (H.obj T) ⊓ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) (pullU φ _ x))
      (hgen (H.obj T) (j PUnit.unit) (j' PUnit.unit))
    simp only [map_mul] at e
    erw [res_pullU_res_eq_res_pullU', res_pullU_res_eq_res_pullU', res_pullU_res_eq_res_pullU'] at e
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    erw [res_res_eq_res_trans, res_res_eq_res_trans, res_res_eq_res_trans]
    exact e
  · have e := congrArg (fun x ↦ res (hle T' j) (pullU φ _ x)) (hcomp (H.obj T) (H.obj T') (H.map a) (j PUnit.unit))
    simp only [map_mul, res_pullU_res_eq_res_pullU', res_res_eq_res_trans] at e
    simp only [res_res_eq_res_trans]
    exact e
