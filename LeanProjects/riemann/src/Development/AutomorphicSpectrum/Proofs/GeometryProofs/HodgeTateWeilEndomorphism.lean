import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtEnd

theorem pullPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.comp_mul, ih]

theorem homPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {Z : Over X} (a : G ⟶ G) [IsMonHom a] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ a = (x ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.mul_comp, ih]

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  haveI : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom a)) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

theorem powDescend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a)
  haveI : Epi ψ := Over.epi_of_epi_left ψ (hk := epiSp a)
  have hψ : ψ ≫ g₀ = g := Over.OverMorphism.ext (by simp [ψ, e])
  apply (cancel_epi ψ).mp
  rw [pullPow, hψ, hg, CategoryTheory.MonObj.comp_one]

theorem secVal_app {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z ⟶ Z')
    (W : Z'.Opens) (f : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) :
    secVal x (φ ⁻¹ᵁ W) h ((φ.app W).hom f) = secVal (x ≫ φ) W h' f := by
  simp only [secVal, Scheme.Hom.comp_appLE]
  rfl

end GlobalTheory.CompanionTheory.Ar.HtEnd

open GlobalTheory.CompanionTheory.Ar.HtEnd in

theorem GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  intro X _ Ω _ _ ξ _ _ G _ _ L n _ hFT ep hW E _ _ M a _ A hA y y' hy hy' hyy' q w hH
  obtain ⟨hw, W, f, hη, P1, P2⟩ := hH
  have hExt : ∀ {e' : E} {v}, M.Extends q e' v → M.Extends q (A e') (v ≫ a) := by
    intro e' v hv
    refine ⟨?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, CategoryTheory.MonObj.one_comp]
    · rw [hA e', Over.comp_left, hv.2]
      erw [Category.assoc]
  have hlat : ∀ e' ∈ M.lat q, A e' ∈ M.lat q := by
    intro e' he'
    have hle : M.lat q ≤ (M.lat q).comap (A.restrictScalars (regAt ξ q)) := by
      refine Submodule.span_le.mpr ?_
      rintro e'' ⟨v, hv⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      exact Submodule.subset_span ⟨v ≫ a, hExt hv⟩
    exact hle he'
  have hw' : ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q := hw
  refine ⟨?_, a.left ⁻¹ᵁ W, (a.left.app W).hom f, ?_, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, (w ∘ₗ A) e' ∈ regAt ξ q
    intro e' he'
    exact hw' (A e') (hlat e' he')
  · have h1 : (η[G] ≫ a).left = (η[G]).left := by rw [IsMonHom.one_hom]
    show a.left ((η[G]).left q.1) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact hη
  · intro k _ _ i xk g c h hx hg hWe
    have h2 : ⊤ ≤ (g.left ≫ a.left) ⁻¹ᵁ W := h
    rw [secVal_app g.left a.left W f h h2]
    obtain ⟨g₀, hg₀⟩ := hFT k i g hg
    have hg₀n : g₀ ^ n = 1 := powDescend i hg₀ hg
    have hga : (g ≫ a) ^ n = 1 := by rw [← homPow, hg, CategoryTheory.MonObj.one_comp]
    have hg₀a : (g₀ ≫ a) ^ n = 1 := by rw [← homPow, hg₀n, CategoryTheory.MonObj.one_comp]
    have hc : (c : k) = i (ep y' g₀) := (hW.weil y' g₀ hy' hg₀n k i xk g c hx hg₀).mp hWe
    rw [hyy' g₀ hg₀n] at hc
    let xk0 : Over.mk (spMap i ≫ ξ) ⟶ G := Over.homMk (spMap i ≫ y.left)
    have hg' : (g ≫ a).left = spMap i ≫ (g₀ ≫ a).left := by
      rw [Over.comp_left, Over.comp_left, hg₀, Category.assoc]
    have hWa := (hW.weil y (g₀ ≫ a) hy hg₀a k i xk0 (g ≫ a) c rfl hg').mpr hc
    exact P1 k i xk0 (g ≫ a) c h2 rfl hga hWa
  · intro e' v hv h
    have h2 : ⊤ ≤ (v.left ≫ a.left) ⁻¹ᵁ W := h
    obtain ⟨r, hr, hE⟩ := P2 (A e') (v ≫ a) (hExt hv) h2
    refine ⟨r, hr, ?_⟩
    rw [LinearMap.comp_apply, secVal_app v.left a.left W f h h2]
    exact hE
