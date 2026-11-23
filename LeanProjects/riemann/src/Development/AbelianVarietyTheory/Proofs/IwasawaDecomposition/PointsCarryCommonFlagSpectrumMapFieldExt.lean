import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

section Helpers

variable {F : Type} [Field F]

theorem spMap_comp_apply_field {Z : Scheme.{0}} {k K : Type} [Field k] [Field K] (σ : k →+* K) (p : Sp k ⟶ Z)
    (w : Sp K) (w' : Sp k) : (spMap σ ≫ p) w = p w' := by
  rw [Scheme.Hom.comp_apply]
  exact congrArg p (Subsingleton.elim (α := PrimeSpectrum k) _ _)

theorem val_spMap_comp_field {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {k K : Type} [Field k]
    [Field K] (σ : k →+* K) (p : Sp k ⟶ M.Z) (y : Ω) : M.val (spMap σ ≫ p) y = σ (M.val p y) := by
  by_cases hy : y ∈ M.O (p (IsLocalRing.closedPoint k))
  · have := RatModel.val_spMap_comp σ p specializes_rfl ⟨y, hy⟩
    rw [RatModel.valLoc_eq_val] at this
    exact this
  · rw [RatModel.val_of_notMem (y := p) (IsLocalRing.closedPoint k) hy, map_zero,
      RatModel.val_of_notMem (y := spMap σ ≫ p) (IsLocalRing.closedPoint K)
        (fun h' => hy (by convert h' using 2; exact (spMap_comp_apply_field σ p _ _).symm))]

theorem bears_spMap {ι : Type} {m : ι → ℕ} {X Y : Var F} (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (A : Mat m X.Fn) {k K : Type} [Field k] [Field K] (σ : k →+* K) (h : Mat m k) (p : Sp k ⟶ Y.X)
    (hb : Bears S φ A h p) : Bears S φ A (h.map σ) (spMap σ ≫ p) := by
  obtain ⟨A', hA', hP⟩ := hb
  refine ⟨A', ?_, ?_⟩
  · convert hA' using 2
    exact spMap_comp_apply_field σ p _ _
  have e : (A' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap σ ≫ p)) =
      ((A' * (A.map φ)⁻¹).map ((ratOf Y).val p)).map σ := by
    funext τ
    ext i j
    exact val_spMap_comp_field (ratOf Y) σ p _
  rw [e, ← Mat.map_inv, ← Mat.map_mul]
  exact hP.map σ fun _ _ => trivial

end Helpers

theorem coBear_spMap : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ _ _ k K _ _ σ x p₁ p₂ hc
  obtain ⟨A, hA, h, hh, h1, h2⟩ := hc
  refine ⟨A, ?_, h.map σ, hh.map σ fun _ _ => trivial, bears_spMap S₁ φ₁ A σ h p₁ h1,
    bears_spMap S₂ φ₂ A σ h p₂ h2⟩
  convert hA using 2
  exact congrArg Eb.S (spMap_comp_apply_field σ x _ _)

end GlobalTheory.FlagBundle
