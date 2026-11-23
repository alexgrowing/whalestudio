import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPointStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.OnSection

theorem not_unitAt_of_eq {F : Type} [Field F] {X Y : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) (W : Dbl Y)
    (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) (τ : ι) (a b : Fin (m τ)) (hab : a ≠ b) {k : Type} [Field k]
    (w : Sp k ⟶ W.Z) (hw : w ≫ W.p₁ = w ≫ W.p₂) (A : Mat m Y.Fn)
    (hA : A ∈ E'.S (W.p₁ (w (IsLocalRing.closedPoint k)))) :
    ¬ UnitAt (w (IsLocalRing.closedPoint k)) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  have hp : W.p₂ (w (IsLocalRing.closedPoint k)) = W.p₁ (w (IsLocalRing.closedPoint k)) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : Sp k ⟶ Y.X => q (IsLocalRing.closedPoint k)) hw.symm).trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨A₀, hA₀⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hM := hf.sub _ A hA A₀ hA₀
  have hd : ∀ σ, (A₀.map φ σ).det ≠ 0 := fun σ => by
    have := Mat.det_map A₀ (φ : X.Fn →+* Y.Fn) σ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA₀ σ))
  generalize hB : A₀.map φ = B at hM hd
  have hB12 : B.map W.α₁ = B.map W.α₂ := by
    subst hB
    funext σ
    ext i j
    exact hα _
  have h1 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₁ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => hq W.p₁ u (mem_O_ratOf.1 hu)
  have h2 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₂ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => by
    obtain ⟨h, e⟩ := hq W.p₂ u (by rw [hp]; exact mem_O_ratOf.1 hu)
    exact ⟨h, e.trans (congrArg (fun q => (ratOf Y).val q u) hw.symm)⟩
  have hN₁ := hM.map W.α₁ fun u hu => (h1 u hu).choose
  have hN₂ := hM.map W.α₂ fun u hu => (h2 u hu).choose
  have hd₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => (Mat.det_map B W.α₂ σ).trans_ne ((map_ne_zero _).2 (hd σ))
  have hg : A.map W.α₁ * (A.map W.α₂)⁻¹ = (A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hB12, Mat.mul_inv_rev, Mat.inv_inv hd₂, mul_assoc,
      ← mul_assoc _ (B.map W.α₂), Mat.inv_mul hd₂, one_mul]
  rw [hg]
  have hG := hN₁.mul hN₂.inv
  let v : W.Z.functionField → k := fun u => if h : u ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k)))
    W.Z.functionField).range then ev ⟨u, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v (x : W.Z.functionField) = ev x := fun x => dif_pos x.2
  have e1 := Par.map_mul_of hG hN₂ v ev hv
  rw [mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one] at e1
  have e2 : ((A * B⁻¹).map W.α₁).map v = ((A * B⁻¹).map W.α₂).map v := by
    funext σ
    ext i j
    obtain ⟨p, hp⟩ := h1 _ ((hM σ).1 i j)
    obtain ⟨q, hq⟩ := h2 _ ((hM σ).1 i j)
    exact ((hv ⟨_, p⟩).trans hp).trans ((hv ⟨_, q⟩).trans hq).symm
  have hV := (Par.map_of hN₂ v ev hv).det_ne
  have e3 : ((A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹).map v = 1 := by
    have := congrArg (· * (((A * B⁻¹).map W.α₂).map v)⁻¹) (e1.symm.trans e2)
    simpa only [mul_assoc, Mat.mul_inv hV, mul_one] using this
  intro hu
  refine (hev ⟨_, (hG τ).1 a b⟩).2 hu ((hv ⟨_, (hG τ).1 a b⟩).symm.trans ?_)
  exact (congrFun (congrFun (congrFun e3 τ) a) b).trans (Matrix.one_apply_ne hab)

end GlobalTheory.FlagPush.OnSection

theorem GlobalTheory.FlagPush.not_unitAt_section : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), a ≠ b → ∀ y : Y.X, ∀ A ∈ E'.S y, ¬ UnitAt (W.δ y) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b hab y A hA
  let w₀ : Sp (Y.X.residueField y) ⟶ Y.X := Y.X.fromSpecResidueField y
  have h0 : w₀ (IsLocalRing.closedPoint _) = y := Scheme.fromSpecResidueField_apply _ _
  have h1 : (w₀ ≫ W.δ) (IsLocalRing.closedPoint _) = W.δ y := (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h0)
  have h2 : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
  have := OnSection.not_unitAt_of_eq hf W hα τ a b hab (w₀ ≫ W.δ)
    (by rw [Category.assoc, Category.assoc, W.δ₁, W.δ₂]) A (by rw [h1, h2]; exact hA)
  rwa [h1] at this
