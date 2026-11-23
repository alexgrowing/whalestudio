import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LieHt.SemiFib

variable {K : Type} [Field K] [NumberField K] (F : SemiFib K)

theorem isUnif_of_fibre {s : K →+* ℂ} {Q : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ F.P₀.A.left}
    {v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)} {g : ℕ} (e : Q.g = g) (u : HolUnif Q.A Q.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} {W : Fin F.P₀.g → Fin g → ℂ} (hP : IsPolFibre s F.P₀ Q ψ) (hA : u.IsAH Hm χ)
    (hw : ∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) : F.IsUnif s u.Λ Hm W :=
  ⟨Q, e, ψ, v', u, χ, hP, rfl, hA, hw⟩

theorem exists_isUnif_posDef (s : K →+* ℂ) :
    ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ) (W : Fin F.P₀.g → Fin F.P₀.g → ℂ),
      F.IsUnif s Λ Hm W ∧ (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).PosDef := by
  obtain ⟨Q, ψ, h⟩ := exists_isPolFibre abelianSchemeLaws_all.1.polBaseChange s F.P₀
  haveI := F.P₀.isAb.comm
  haveI := Q.isAb.comm
  haveI := F.P₀.smoothDim
  obtain ⟨v', hb, hv'⟩ := exists_isLieBasis_baseChange K ℂ s F.P₀.A Q.A ψ h.2.1
    (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := thetaUnifAV_all Q rig hrig
  choose W hW using fun i => (hd _ (hb.1 i)).exists
  have hpd := CM.LieMetric.posDef_gram hA.1 hA.2.1 (CM.LieMetric.linearIndependent_of_isLieBasis u hd' hb hW)
  clear hd hd'
  revert u Hm χ W
  rw [h.1]
  intro u Hm χ hA W hW hpd
  exact ⟨_, Hm, W, isUnif_of_fibre F h.1 u h hA fun i => ⟨hv' i, hW i⟩, hpd⟩

theorem exists_isHerm : ∃ h, F.IsHerm h := by
  choose Λ Hm W hU hG using F.exists_isUnif_posDef
  exact ⟨CM.LieMetric.ofGram _ hG, fun s => ⟨Λ s, Hm s, W s, hU s, fun i j => by
    rw [CM.LieMetric.ofGram_single, Matrix.of_apply]⟩⟩

theorem exists_isLeast_hermLength {g : ℕ} (hg : 0 < g) (Λ : Submodule ℤ (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) :
    ∃ t : ℝ, IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} t ∧ 0 < t := by
  set q : (Fin g → ℂ) → ℝ := fun z => (hermForm Hm z z).re with hq
  have hqc : Continuous q := by
    simp only [hq, hermForm, dotProduct, Matrix.mulVec]
    fun_prop
  have hsm : ∀ (c : ℝ) (z : Fin g → ℂ), q (c • z) = c ^ 2 * q z := fun c z => by
    simp only [hq, hermForm, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul, star_trivial]
    simp [Complex.smul_re]
    ring
  haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hqc.continuousOn
  have hz₁0 : z₁ ≠ 0 := by
    rintro rfl
    simp at hz₁
  have hm : 0 < q z₁ := hp z₁ hz₁0
  have hlow : ∀ z : Fin g → ℂ, ‖z‖ ^ 2 * q z₁ ≤ q z := fun z => by
    rcases eq_or_ne z 0 with rfl | hz
    · simp [hq, hermForm]
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h1 : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
    have h2 : q z₁ ≤ q (‖z‖⁻¹ • z) := hmin h1
    rw [hsm] at h2
    have h3 : q z = ‖z‖ ^ 2 * ((‖z‖⁻¹) ^ 2 * q z) := by
      rw [← _root_.mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne', one_pow, _root_.one_mul]
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  obtain ⟨z₀, hz₀, hz₀0⟩ : ∃ z ∈ Λ, z ≠ 0 := by
    by_contra! h
    have h2 : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ ⊥ := by
      rw [Submodule.span_le]
      intro z hz
      simp [h z hz]
    rw [hfull, top_le_iff] at h2
    exact bot_ne_top h2
  set T : Set (Fin g → ℂ) := {z | z ∈ Λ ∧ z ≠ 0 ∧ q z ≤ q z₀} with hT
  have hclosed : IsClosed (Λ : Set (Fin g → ℂ)) := by
    haveI : DiscreteTopology Λ.toAddSubgroup := hd
    exact AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
  have hdisc : _root_.IsDiscrete (Λ : Set (Fin g → ℂ)) := isDiscrete_iff_discreteTopology.2 hd
  have hfin : T.Finite := by
    refine (Metric.finite_isBounded_inter_isClosed hdisc (Metric.isBounded_closedBall (x := (0 : Fin g → ℂ))
      (r := √(q z₀ / q z₁))) hclosed).subset fun z hz => ⟨?_, hz.1⟩
    rw [mem_closedBall_zero_iff]
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hm]
    exact (hlow z).trans hz.2.2
  obtain ⟨a, ha, hamin⟩ := Set.exists_min_image T q hfin ⟨z₀, hz₀, hz₀0, le_rfl⟩
  refine ⟨√(q a), ⟨⟨a, ha.1, ha.2.1, rfl⟩, ?_⟩, Real.sqrt_pos.2 (hp a ha.2.1)⟩
  rintro t ⟨z, hz, hz0, rfl⟩
  refine Real.sqrt_le_sqrt ?_
  by_cases hle : q z ≤ q z₀
  · exact hamin z ⟨hz, hz0, hle⟩
  · exact (ha.2.2.trans (not_le.1 hle).le)

theorem exists_isRho (hg : 0 < F.P₀.g) : ∃ ρ : (K →+* ℂ) → ℝ, F.IsRho ρ ∧ ∀ σ, 0 < ρ σ := by
  have key : ∀ s : K →+* ℂ, ∃ t : ℝ, 0 < t ∧ ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
      (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
        IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} t := fun s => by
    obtain ⟨Λ, Hm, W, hU, -⟩ := F.exists_isUnif_posDef s
    obtain ⟨Q, e, ψ, v', u, χ, hP, hΛ, hA, -⟩ := id hU
    subst hΛ
    haveI := u.discrete
    obtain ⟨t, ht, hpos⟩ := exists_isLeast_hermLength hg u.Λ u.full hA.2.1
    exact ⟨t, hpos, u.Λ, Hm, W, hU, ht⟩
  choose ρ hρ H using key
  exact ⟨ρ, fun s => H s, hρ⟩

end GlobalTheory.LieHt.SemiFib
end
