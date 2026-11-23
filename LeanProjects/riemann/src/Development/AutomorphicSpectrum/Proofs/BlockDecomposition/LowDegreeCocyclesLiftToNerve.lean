import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.LowDict

theorem exists_quot_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (K : Submodule R M) (Z : Submodule R N) (hK : ∀ x, x ∈ K ↔ e x ∈ Z)
    (BK : Submodule R K) (BZ' : Submodule R Z)
    (hB : ∀ (x : K) (f : Z), e x.1 = f.1 → (x ∈ BK ↔ f ∈ BZ')) :
    ∃ u : (Z ⧸ BZ') ≃ₗ[R] (K ⧸ BK),
      (∀ (f : Z) (x : K), e x.1 = f.1 → u (BZ'.mkQ f) = BK.mkQ x) ∧ ∀ f : Z, ∃ x : K, e x.1 = f.1 := by
  have hmap : K.map (e : M →ₗ[R] N) = Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨e.symm y, (hK _).2 (by simpa using hy), by simp⟩
  let v : K ≃ₗ[R] Z := e.ofSubmodules K Z hmap
  have hv : ∀ x : K, (v x).1 = e x.1 := fun _ ↦ rfl
  have hq : BZ'.map (v.symm : Z →ₗ[R] K) = BK := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine (hB _ f ?_).2 hf
      rw [← hv]
      simp
    · intro hx
      exact ⟨v x, (hB x (v x) (hv x).symm).1 hx, by simp⟩
  refine ⟨Submodule.Quotient.equiv BZ' BK v.symm hq, fun f x h ↦ ?_, fun f ↦ ⟨v.symm f, ?_⟩⟩
  · have hx : v.symm f = x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext h.symm
    rw [← hx]
    rfl
  · rw [← hv]
    simp

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

theorem Z2_eq_ker : Z2 F = LinearMap.ker (d2 F) := by
  ext z
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · refine LinearMap.mem_ker.2 ?_
    funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.1 h) T) T') T'') T''') φ) ψ) χ
    rw [d2_apply] at this
    simp only [Pi.zero_apply] at this
    linear_combination -this

theorem dict_low : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∃ (u₁ : H1 F ≃ₗ[R] HH F 1) (u₂ : H2 F ≃ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁.toLinearMap ∧ IsDegreeTwoComparison F u₂.toLinearMap ∧
      (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) ∧
      (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) := by
  intro hD R _ C _ F
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, -, h₀, h₁, h₂⟩ := hD R C F
  have k₁ : ∀ x, x ∈ Zc F 1 ↔ e₁ x ∈ Z1 F := fun x ↦ by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₁, LinearEquiv.map_eq_zero_iff]
  have k₂ : ∀ x, x ∈ Zc F 2 ↔ e₂ x ∈ Z2 F := fun x ↦ by
    rw [Z2_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₂, LinearEquiv.map_eq_zero_iff]
  have b₁ : ∀ (x : Zc F 1) (f : Z1 F), e₁ x.1 = f.1 →
      (x ∈ BZ F 1 ↔ f ∈ LinearMap.range ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₀ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₀, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₀.symm g, e₁.injective ?_⟩
      rw [h₀, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  have b₂ : ∀ (x : Zc F 2) (f : Z2 F), e₂ x.1 = f.1 →
      (x ∈ BZ F 2 ↔ f ∈ LinearMap.range ((d1 F).codRestrict (Z2 F) (differential_one_mem_scaled_lattice F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₁ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₁, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₁.symm g, e₂.injective ?_⟩
      rw [h₁, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  obtain ⟨u₁, c₁, s₁⟩ := exists_quot_equiv e₁ (Zc F 1) (Z1 F) k₁ (BZ F 1) _ b₁
  obtain ⟨u₂, c₂, s₂⟩ := exists_quot_equiv e₂ (Zc F 2) (Z2 F) k₂ (BZ F 2) _ b₂
  refine ⟨u₁, u₂, fun f x hx ↦ c₁ f x ?_, fun f x hx ↦ c₂ f x ?_, fun f ↦ ?_, fun f ↦ ?_⟩
  · funext T T' φ
    exact (v₁ x.1 T T' φ).trans (hx T T' φ)
  · funext T T' T'' φ ψ
    exact (v₂ x.1 T T' T'' φ ψ).trans (hx T T' T'' φ ψ)
  · obtain ⟨x, hx⟩ := s₁ f
    exact ⟨x, fun T T' φ ↦ (v₁ x.1 T T' φ).symm.trans (congrFun (congrFun (congrFun hx T) T') φ)⟩
  · obtain ⟨x, hx⟩ := s₂ f
    exact ⟨x, fun T T' T'' φ ψ ↦ (v₂ x.1 T T' T'' φ ψ).symm.trans
      (congrFun (congrFun (congrFun (congrFun (congrFun hx T) T') T'') φ) ψ)⟩

end GlobalTheory.CompanionTheory.HopfC.LowDict
