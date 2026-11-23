import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModelOfIsLieBasis

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HolFac

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

private theorem spMap_appLE_comp_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    spMap ((x.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom) ≫ hW.fromSpec = x := by
  have key := IsAffineOpen.SpecMap_appLE_fromSpec x hW
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at key
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, key]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem exists_ringMaps_of_hol : ∀ (X : Scheme.{0}) (W : X.Opens) (hW : IsAffineOpen W) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ⊤ ≤ p 0 ⁻¹ᵁ W →
    ∃ (ρ : ℝ) (ψ : (Fin n → ℂ) → (Γ(X, W) →+* ℂ)), 0 < ρ ∧ ρ ≤ 1 ∧ Flat.IsHolPts (Metric.ball 0 1) ψ ∧
      ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hW.fromSpec = p ((ρ : ℂ) • z) := by
  intro X W hW n p hp h0
  classical
  obtain ⟨hSo, -⟩ := hp W 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρpos, hρ1, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, min_le_left _ _⟩
  have hmaps : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈
      {b | b ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ⊤ ≤ (TopologicalSpace.Opens.map (p b).base).obj W} := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρpos.le]
    calc ρ * ‖z‖ < ρ * 1 := mul_lt_mul_of_pos_left hz hρpos
      _ = ρ := mul_one ρ
      _ ≤ ε := hρε
  let φ : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ W → (Γ(X, W) →+* ℂ) := fun x hx =>
    (x.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
  refine ⟨ρ, fun z => if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0,
    hρpos, hρ1, ⟨Metric.isOpen_ball, ?_⟩, ?_⟩
  · intro r
    have hlin : DifferentiableOn ℂ (fun b : Fin n → ℂ => (ρ : ℂ) • b) (Metric.ball 0 1) :=
      differentiableOn_id.const_smul (ρ : ℂ)
    have hd := (hp W r).2.comp hlin hmaps
    refine hd.congr ?_
    intro z hz
    have hzS : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W := (hmaps z hz).2
    show (if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0) r = valR (p ((ρ : ℂ) • z)) W r
    rw [dif_pos hzS]
    unfold valR
    rw [dif_pos hzS]
    rfl
  · intro z hz
    have hzS : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W := (hmaps z hz).2
    show spMap (if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0) ≫ hW.fromSpec = _
    rw [dif_pos hzS]
    exact spMap_appLE_comp_fromSpec hW _ hzS

end GlobalTheory.CompanionTheory.Ar.HolFac
