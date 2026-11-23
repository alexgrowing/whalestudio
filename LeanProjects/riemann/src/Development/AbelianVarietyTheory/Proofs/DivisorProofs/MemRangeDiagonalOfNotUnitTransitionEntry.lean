import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPointStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem mem_range_section_of_not_unitAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)) (z : W.Z), ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) → ¬ UnitAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) → z ∈ Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b z
  obtain ⟨k, _, w, rfl⟩ : ∃ (k : Type) (_ : Field k) (w : Sp k ⟶ W.Z), w (IsLocalRing.closedPoint k) = z :=
    ⟨W.Z.residueField z, inferInstance, W.Z.fromSpecResidueField z, Scheme.fromSpecResidueField_apply _ _⟩
  intro A₁ hA₁ A₂ hA₂ hlow hnu
  have hbase : W.p₁ ≫ f = W.p₂ ≫ f := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hf.hom W hα
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  refine W.diag k w ?_
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hff : f (W.p₂ (w (IsLocalRing.closedPoint k))) = f (W.p₁ (w (IsLocalRing.closedPoint k))) := by
    rw [← Scheme.Hom.comp_apply W.p₂ f, ← hbase, Scheme.Hom.comp_apply]
  have hM₁ := hf.sub _ A₁ hA₁ A hA
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun y => A ∈ E.S y) hff).mpr hA)
  let v : W.Z.functionField → k := fun x =>
    if h : x ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range then ev ⟨x, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v x = ev x := fun x => dif_pos x.2
  have hN₁ := hM₁.map W.α₁ fun x hx => (hq W.p₁ x (mem_O_ratOf.1 hx)).1
  have hN₂ := hM₂.map W.α₂ fun x hx => (hq W.p₂ x (mem_O_ratOf.1 hx)).1
  have e₁ : ((A₁ * (A.map φ)⁻¹).map W.α₁).map v = (A₁ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₁)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₁ _ (mem_O_ratOf.1 ((hM₁ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have e₂ : ((A₂ * (A.map φ)⁻¹).map W.α₂).map v = (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₂)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₂ _ (mem_O_ratOf.1 ((hM₂ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have hC : (A.map φ).map W.α₁ = (A.map φ).map W.α₂ := by
    funext σ
    ext i j
    exact hα _
  have hCd : ∀ σ, (((A.map φ).map W.α₂)⁻¹ σ).det ≠ 0 := fun σ => by
    have h := hN₂.det_ne σ
    rw [Mat.map_mul, Mat.map_inv, Pi.mul_apply, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  have hg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      (A₁ * (A.map φ)⁻¹).map W.α₁ * ((A₂ * (A.map φ)⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hC, Mat.mul_inv_rev, mul_assoc, ← mul_assoc _ _ (A₂.map W.α₂)⁻¹,
      Mat.mul_inv hCd, one_mul]
  have hG := hN₁.mul hN₂.inv
  rw [hg] at hlow hnu
  generalize hN1 : (A₁ * (A.map φ)⁻¹).map W.α₁ = N₁ at *
  generalize hN2 : (A₂ * (A.map φ)⁻¹).map W.α₂ = N₂ at *
  have hb₁ := hN₁.map_of v ev hv
  have hb₂ := hN₂.map_of v ev hv
  have hbG := hG.map_of v ev hv
  have hmul : (N₁ * N₂⁻¹).map v * N₂.map v = N₁.map v := by
    rw [← hG.map_mul_of hN₂ v ev hv, mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one]
  have hv0 : v 0 = 0 := (hv 0).trans (map_zero ev)
  have hlowv : Par m ⊤ ((N₁ * N₂⁻¹).map v) := fun σ => by
    refine ⟨(hbG σ).1, (hbG σ).2.1, (hbG σ).2.2.1, fun i j _ hij => ?_⟩
    show v ((N₁ * N₂⁻¹) σ i j) = 0
    by_cases hc : (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩
    · obtain ⟨h1, h2⟩ := hc
      cases h1
      have h3 : j = b := eq_of_heq (Sigma.mk.inj h2).2
      subst h3
      by_contra h0
      exact hnu ((hev ⟨_, (hG τ).1 a j⟩).1 fun h => h0 ((hv ⟨_, (hG τ).1 a j⟩).trans h))
    · rw [hlow.2.2 σ i j hij hc, hv0]
  have hA' : A ∈ E.S ((w ≫ W.p₁ ≫ f) (IsLocalRing.closedPoint k)) :=
    (congrArg (fun y => A ∈ E.S y) ((Scheme.Hom.comp_apply w (W.p₁ ≫ f) _).trans
      (Scheme.Hom.comp_apply W.p₁ f _))).mpr hA
  refine (hf.lifts k (w ≫ W.p₁ ≫ f) A hA' (N₁.map v) hb₁).unique ⟨Category.assoc _ _ _, A₁, ?_, ?_⟩
    ⟨(Category.assoc _ _ _).trans (congrArg (w ≫ ·) hbase.symm), A₂, ?_, ?_⟩
  · exact (congrArg (fun y => A₁ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₁ _)).mpr hA₁
  · have : Par m ⊤ (N₁.map v * (N₁.map v)⁻¹) := by rw [Mat.mul_inv hb₁.det_ne]; exact Par.one
    exact e₁ ▸ this
  · exact (congrArg (fun y => A₂ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₂ _)).mpr hA₂
  · have : Par m ⊤ (N₁.map v * (N₂.map v)⁻¹) := by
      rw [← hmul, mul_assoc, Mat.mul_inv hb₂.det_ne, mul_one]; exact hlowv
    exact e₂ ▸ this

end GlobalTheory.FlagPush
