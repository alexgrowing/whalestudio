import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

private theorem finsum_norm_ne_zero {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    (Γ : Subgroup X) [DiscreteTopology Γ] (f : X → ℂ) (hf : HasCompactSupport f) (a b δ : X) (hδ : δ ∈ Γ)
    (h : f (a * δ * b) ≠ 0) : ∑ᶠ γ : Γ, ((‖f (a * γ * b)‖ : ℝ) : ℂ) ≠ 0 := by
  have hc : IsCompact ((fun y => a⁻¹ * y * b⁻¹) '' tsupport f) := hf.isCompact.image (by fun_prop)
  have hfin : ((fun γ : Γ => (γ : X)) ⁻¹' ((fun y => a⁻¹ * y * b⁻¹) '' tsupport f)).Finite := by
    have := Γ.tendsto_coe_cofinite_of_discrete ⟨inferInstance⟩ hc.compl_mem_cocompact
    simpa [Filter.mem_map, Filter.mem_cofinite] using this
  have hs : (Function.support fun γ : Γ => ‖f (a * γ * b)‖).Finite := by
    refine hfin.subset fun γ hγ => ⟨a * γ * b, subset_tsupport _ ?_, by group⟩
    simpa using hγ
  have h1 : ∑ᶠ γ : Γ, ((‖f (a * γ * b)‖ : ℝ) : ℂ) = ((∑ᶠ γ : Γ, ‖f (a * γ * b)‖ : ℝ) : ℂ) :=
    (Complex.ofRealHom.toAddMonoidHom.map_finsum hs).symm
  rw [h1, Complex.ofReal_ne_zero]
  exact (finsum_pos (f := fun γ : Γ => ‖f (a * γ * b)‖) (fun _ => norm_nonneg _) ⟨⟨δ, hδ⟩, norm_pos_iff.2 h⟩ hs).ne'

theorem UpperTheory.exists_height_bound_of_twistedElliptic_support :
    G2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ f : CC E n, Ell σ f → ∃ R : ℝ, ∀ x : G1 E n, ∀ δ ∈ Gam E n, f (x⁻¹ * δ * θ.e x) ≠ 0 → qht x ≤ R := by
  intro h2 F E _ _ _ _ _ _ σ hσ n hn μ _ θ hθ f hf
  obtain ⟨C, c, hC⟩ := h2 F E σ hσ n hn
  have hcs : HasCompactSupport (f : G1 E n → ℂ) := f.hasCompactSupport
  obtain ⟨M, hM⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_height_le_of_isCompact
    (hcs.isCompact.image (continuous_subtype_val (p := fun g => g ∈ normOneGL E n)))
  let f' : PositivityTheory.Rg.Tf.Core.CC E n :=
    { toFun := fun g => ((‖f g‖ : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp (map_continuous f).norm
      hasCompactSupport' := hcs.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp) }
  have hne : ∀ g, f' g ≠ 0 → f g ≠ 0 := fun g hg h0 => hg (by
    show ((‖f g‖ : ℝ) : ℂ) = 0
    simp [h0])
  refine ⟨C * (max 1 M) ^ c, fun x δ hδ hx => ?_⟩
  refine hC μ θ hθ f' (max 1 M) (le_max_left _ _) (fun g hg => ?_) (fun δ x y hy hg => hf δ x y hy (hne y hg)) x ?_
  · exact (hM _ ⟨g, subset_tsupport _ (hne g hg), rfl⟩).trans (le_max_right _ _)
  · exact finsum_norm_ne_zero (Gam E n) f hcs x⁻¹ (θ.e x) δ hδ hx
