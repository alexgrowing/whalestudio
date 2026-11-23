import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingRotBlock

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.ImageHeightNonneg

theorem IsImageHeight.neg_log_le {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d n : ℕ} {w : Fin n → V} {abelian₂ h : ℝ} (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : Submodule.span (𝓞 K) (Set.range w) = L) (hle : ∀ i σ, Nm σ (w i) ≤ abelian₂) (hh : IsImageHeight Nm L ev d h) :
    0 ≤ h + Real.log abelian₂ := by
  obtain ⟨N, n', b, w', A, δ, f, hF, hf, e⟩ := hh
  have hF' : IsFrame Nm L b (Matrix.of fun j k => b.repr (w k) j) A := by
    refine ⟨?_, ?_, hF.herm, hF.conj, hF.norm⟩
    · simp only [Matrix.of_apply, Module.Basis.sum_repr]; exact hw
    · have h1 : Submodule.span K (Set.range w) = ⊤ := by rw [← hs, ← hw, Submodule.span_span_of_tower]
      have h2 := congrArg (Submodule.map b.equivFun.toLinearMap) h1
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
      exact h2
  have h1 := GlobalTheory.ImageHeightUnique.formHeight_linSubst hF hF' δ f
  rw [Module.Basis.toMatrix_self, GlobalTheory.HeightUnique.linSubst_one] at h1
  obtain ⟨y, hy, -⟩ := hf.exists_point
  obtain ⟨j, -⟩ := Function.ne_iff.1 hy
  have h2 := GlobalTheory.FormHtLower.formHeight_ge (Λ := abelian₂) (Fin.pos j) hF'.full hF'.herm
    (fun k σ => (hF.norm σ (w k)).trans_le (hle k σ)) hf.ne_zero hf.homog
  rw [h1, ← e] at h2
  have hpos : (0 : ℝ) < ((d : ℝ) + 1) * δ := mul_pos (by positivity) (Nat.cast_pos.2 hf.pos)
  refine nonneg_of_mul_nonneg_right (a := ((d : ℝ) + 1) * δ) ?_ hpos
  push_cast at h2
  linarith

theorem imageHeight_add_log_nonneg (K V Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ) (hG : HasGram Nm)
    (hc : ∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : IsShortGen Nm L w abelian₂) (hd : 0 < imageDeg ev d) : 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ := by
  have hL : Submodule.span (𝓞 K) (Set.range w) = L :=
    le_antisymm (Submodule.span_le.2 fun x hx => (hw.gen x).2 (Submodule.subset_span hx))
      fun x hx => Submodule.span_le_restrictScalars ℤ (𝓞 K) _ ((hw.gen x).1 hx)
  have hK : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ h =>
    IsTotallyComplex.complexEmbedding_not_isReal σ h
  exact IsImageHeight.neg_log_le hs hL hw.le (isImageHeight_imageHeight (exists_isImageHeight_iff.2
    ⟨exists_isFrame hK hc hG (hL ▸ Submodule.fg_span (Set.finite_range _)) hs, hd⟩))

theorem imageHeight_nonneg : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → Submodule.span K (L : Set V) = ⊤ → IsShortGen Nm L w abelian₂ → 0 < imageDeg ev d → 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ :=
  fun _ => imageHeight_add_log_nonneg

end GlobalTheory.ImageHeightNonneg
