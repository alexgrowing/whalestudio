import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem val_spMap_pt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (σ : Ω →+* K) (x : Ω) : M.val (spMap σ ≫ M.pt) x = σ x := by
  have hx : x ∈ M.O (genericPoint M.Z) := by rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have := M.val_spMap_comp σ M.pt (M.pt_specializes _ _) ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val, RatModel.val_pt] at this
  exact this

theorem flag_conv : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hR B hB A hA K _ ψ₁ ψ₂ U hpt hBe
  have hom : (ratOf Y).pt ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hR.hom
  have key : ∀ σ : Y.Fn →+* K, spMap σ ≫ (ratOf Y).pt ≫ f = spMap (σ.comp φ.toRingHom) ≫ (ratOf X).pt := by
    intro σ
    rw [hom]
    show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map (CommRingCat.ofHom (σ.comp φ.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).symm
  have h1 : ∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u) := by
    intro u
    have e1 := val_spMap_pt (ratOf X) (ψ₁.comp φ.toRingHom) u
    have e2 := val_spMap_pt (ratOf X) (ψ₂.comp φ.toRingHom) u
    rw [← key, hpt, key] at e1
    exact e1.symm.trans e2
  refine ⟨h1, ?_⟩
  obtain ⟨A', hA', hP⟩ := hBe
  have hgen : (spMap ψ₂ ≫ (ratOf Y).pt) (IsLocalRing.closedPoint K) = genericPoint Y.X :=
    (ratOf Y).pt_apply _
  rw [hgen] at hA'
  have hval : (ratOf Y).val (spMap ψ₂ ≫ (ratOf Y).pt) = ψ₂ := funext (val_spMap_pt (ratOf Y) ψ₂)
  rw [hval] at hP
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hBd : ∀ τ, (B τ).det ≠ 0 := Fr.det_ne hB
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  set C : Mat m Y.Fn := A.map φ with hC
  have hCd : ∀ τ, (C τ).det ≠ 0 := fun τ => by
    rw [hC]; exact fun h0 => (map_ne_zero φ.toRingHom).2 (hAd τ) ((Mat.det_map A φ.toRingHom τ).symm.trans h0)
  have hCψ : C.map ψ₁ = C.map ψ₂ := by
    funext τ; ext i j; exact h1 (A τ i j)
  have hC2d : ∀ τ, (C.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hCd τ)
  have hA'2d : ∀ τ, (A'.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA'd τ)
  have e : U * (B * C⁻¹).map ψ₁ * ((A' * C⁻¹).map ψ₂)⁻¹ = U * B.map ψ₁ * (A'.map ψ₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hCψ, Mat.mul_inv_rev, Mat.inv_inv hC2d]
    rw [mul_assoc U, mul_assoc (B.map ψ₁), ← mul_assoc (C.map ψ₂)⁻¹, Mat.inv_mul hC2d, one_mul, ← mul_assoc]
  rw [e] at hP
  have hQ : Par m (⊤ : Subring K) ((A' * B⁻¹).map ψ₂) := by
    have := (Fr.mem_iff hB).1 hA'
    exact this.map ψ₂ (fun _ _ => trivial)
  have := hP.mul hQ
  rw [Mat.map_mul, Mat.map_inv] at this
  have e2 : U * B.map ψ₁ * (A'.map ψ₂)⁻¹ * (A'.map ψ₂ * (B.map ψ₂)⁻¹) = U * (B.map ψ₁ * (B.map ψ₂)⁻¹) := by
    rw [mul_assoc (U * B.map ψ₁), ← mul_assoc (A'.map ψ₂)⁻¹, Mat.inv_mul hA'2d, one_mul, mul_assoc]
  rwa [e2] at this

end GlobalTheory.FlagPush
