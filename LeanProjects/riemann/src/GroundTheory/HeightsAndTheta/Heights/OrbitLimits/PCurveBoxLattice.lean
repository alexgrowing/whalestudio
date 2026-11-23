import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxLattice
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveFieldNumber
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveEmbedOrbit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartLatFull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem chartRadius_smul (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (d : K → ℂ) (hd : ∀ k, d k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => d p.1 * z p) = chartRadius A c z := by
  unfold chartRadius
  rw [A.smul d z hd]
  have hX : (∏ k, ‖d k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd k))
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  rw [mul_div_mul_left _ _ hX]

omit [∀ k, Fintype (ι k)] in

theorem chartRadius_conj (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsConjInvariantH A) (c : ∀ k, ι k)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => (starRingEnd ℂ) (z p)) = chartRadius A c z := by
  unfold chartRadius
  rw [hA z]
  simp only [Complex.norm_conj]

omit [∀ k, Fintype (ι k)] in

theorem chartRadius_pos (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) : 0 < chartRadius A c z :=
  div_pos (A.pos z fun k => ⟨c k, hz k⟩)
    (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hz k)) _)

end Lemmas

theorem genIndex_map_addEquiv {G : Type*} [AddCommGroup G] (m : G ≃+ G) (A B : AddSubgroup G) :
    genIndex (A.map m.toAddMonoidHom) (B.map m.toAddMonoidHom) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ m.injective,
    AddSubgroup.relIndex_map_map_of_injective _ _ m.injective]

theorem addSubgroup_fg_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] {A : AddSubgroup G} (hA : A.FG)
    (f : G →+ H) : (A.map f).FG := by
  classical
  obtain ⟨S, hS⟩ := hA
  exact ⟨S.image f, by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]⟩

theorem CurveBoxLattice.proof (hF : CurveFieldNumber.Statement) (hE : CurveEmbedOrbit.Statement)
    (hL : ChartLatFull.Statement) (hN : NumberFieldBoxCount.Statement)
    (hG : HilbertSamuel.SectionLatticeFinite.Statement) : CurveBoxLattice.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  have : NumberField Ω := hF K ι Ω y hP hB
  obtain ⟨e, he⟩ := hE K ι Ω y R hP hB hR hRu
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have hBeq : (curveRing y).toAddSubgroup = chartLat y 0 0 := by
    ext s
    simp [mem_curveRing, chartLat]
  have hBfg : (curveRing y).toAddSubgroup.FG := hBeq ▸ hG K ι Ω y 0 0 hy
  have hBfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ (curveRing y).toAddSubgroup :=
    hBeq ▸ hL K ι Ω y hB 0 0
  obtain ⟨C, hC⟩ := hN Ω _ hBfg hBfull
  refine ⟨C, fun τ _ => ?_⟩
  have hu : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  set u := chartUnit y c A.a τ with hu_def
  let m : Ω ≃+ Ω :=
    { toFun := fun x => x / u
      invFun := fun x => x * u
      left_inv := fun x => div_mul_cancel₀ x hu
      right_inv := fun x => mul_div_cancel_right₀ x hu
      map_add' := fun x z => add_div x z u }
  set Λ := (chartLat y A.a τ).map m.toAddMonoidHom with hΛ
  have hΛfg : Λ.FG := addSubgroup_fg_map (hG K ι Ω y A.a τ hy) _
  have hΛfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ Λ := by
    intro x
    obtain ⟨n, hn, hmem⟩ := hL K ι Ω y hB A.a τ (x * u)
    refine ⟨n, hn, ?_⟩
    have : (n : Ω) * x = m ((n : Ω) * (x * u)) := by
      show (n : Ω) * x = (n : Ω) * (x * u) / u
      rw [mul_div_assoc, mul_div_cancel_right₀ x hu]
    rw [this]
    exact AddSubgroup.mem_map_of_mem _ hmem
  have hBmap : (curveMul y u).map m.toAddMonoidHom = (curveRing y).toAddSubgroup := by
    rw [curveMul, AddSubgroup.map_map]
    convert AddSubgroup.map_id _ using 2
    ext x
    show u * x / u = x
    rw [mul_div_cancel_left₀ x hu]
  have hidx : genIndex Λ (curveRing y).toAddSubgroup = genIndex (chartLat y A.a τ) (curveMul y u) := by
    rw [← hBmap, hΛ, genIndex_map_addEquiv]
  let ρ : (Ω →+* ℂ) → ℝ := fun σ => chartRadius A c (fun p => σ (y p)) ^ τ
  have hρpos : ∀ σ, 0 < ρ σ := fun σ =>
    pow_pos (chartRadius_pos A c _ fun k => (map_ne_zero σ).mpr (hc k)) τ
  have hρconj : ∀ σ, ρ (NumberField.ComplexEmbedding.conjugate σ) = ρ σ := by
    intro σ
    simp only [ρ, NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [chartRadius_conj A hA c]
  have hcount := hC Λ hΛfg hΛfull ρ hρpos hρconj
  have hsum : ∑ t ∈ R, Real.log (chartRadius A c t) =
      ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨d, hd, ht⟩ := he t
    rw [ht, chartRadius_smul A c d hd]
  have hρsum : ∑ σ : Ω →+* ℂ, Real.log (ρ σ) =
      (τ : ℝ) * ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Real.log_pow _ _
  have hcard : Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / u)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ} =
      Nat.card {x : Λ // ∀ σ : Ω →+* ℂ, ‖σ (x : Ω)‖ ≤ ρ σ} :=
    Nat.card_congr ((AddSubgroup.equivMapOfInjective _ m.toAddMonoidHom m.injective).toEquiv.subtypeEquiv
      fun s => Iff.rfl)
  rw [hcard, hsum, ← hρsum, chartIndexLog, ← hu_def, ← hidx]
  exact hcount

end GroundTheory.Heights₂.Heights.Targets
