import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanValueBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompareStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.FlatLine

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]

theorem aeval_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (MvPolynomial.comp_aeval_apply (R := ℤ) z σ.toIntAlgHom f).symm

theorem ptsOver_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) : (fun p => σ (z p)) ∈ ptsOver 𝕜 P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_embed, hz.2 f hf, map_zero]

theorem hasVal_embed {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜)
    {z : (Σ k, ι k) → L} {val : L} (h : HasVal y a u z val) : HasVal y a u (fun p => σ (z p)) (σ val) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_embed]
    exact (map_ne_zero σ).2 hfz
  · rw [aeval_embed, aeval_embed, hgz, map_mul]

theorem isSmoothHerm_powH {A : HermLine ι} (hA : IsSmoothHerm A) (k : ℕ) : IsSmoothHerm (powH A k) :=
  ContDiffOn.pow hA k

theorem ptHt_pow (A : HermLine ι) (k : ℕ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) :
    ptHt (fun b => (((k : ℤ) * A.a b : ℤ) : ℝ)) (fun z => (k : ℝ) * Real.log (A.h z)) L w = k * lineHt A L w := by
  have e : ∀ v : FinitePlace L, ∑ b, (((k : ℤ) * A.a b : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) =
      (k : ℝ) • ∑ b, (A.a b : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  simp only [ptHt, lineHt, e]
  rw [← smul_finsum, ← Finset.mul_sum, smul_eq_mul]
  ring

theorem exists_arch_bound {y : (Σ k, ι k) → Ω} {d : ℕ} (hAr : IsArithVar (mCoordIdeal y) d) (hB : Birational y)
    {A : HermLine ι} {k : ℕ} {u : Ω} {c : ℝ} (hS : IsSmoothHerm A)
    (hV : VertBound y (fun b => k * A.a b) u c) :
    ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, val ≠ 0 → HasVal y (fun b => k * A.a b) u z val →
      |(k : ℝ) * Real.log (A.h z) - Real.log ‖val‖| ≤ C := by
  obtain ⟨hu, q, m, hq, hm, -, h1, h2⟩ := hV
  have hP := isSmoothHerm_powH hS k
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hAr hB (powH A k) q m u hP hq hm h1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hAr hB (powH A k).inv q m u⁻¹ (isSmoothHerm_inv hP) hq hm h2
  refine ⟨max C₁ C₂, fun z hz val hv hval => ?_⟩
  have hp : 0 < A.h z := A.pos z hz.1
  have hn : 0 < ‖val‖ := norm_pos_iff.2 hv
  have b₁ : ‖val‖ ≤ Real.exp C₁ * A.h z ^ k := hC₁ z hz val hval
  have b₂ : ‖val⁻¹‖ ≤ Real.exp C₂ * (A.h z ^ k)⁻¹ := hC₂ z hz val⁻¹ (hasVal_inv hu hz hv hval)
  have l₁ : Real.log ‖val‖ ≤ C₁ + k * Real.log (A.h z) := by
    have := Real.log_le_log hn b₁
    rwa [Real.log_mul (Real.exp_pos _).ne' (pow_pos hp k).ne', Real.log_exp, Real.log_pow] at this
  have l₂ : -Real.log ‖val‖ ≤ C₂ - k * Real.log (A.h z) := by
    have := Real.log_le_log (norm_pos_iff.2 (inv_ne_zero hv)) b₂
    rwa [norm_inv, Real.log_inv, Real.log_mul (Real.exp_pos _).ne' (inv_pos.2 (pow_pos hp k)).ne', Real.log_exp,
      Real.log_inv, Real.log_pow, ← sub_eq_add_neg] at this
  rw [abs_le]
  constructor
  · have := le_max_left C₁ C₂
    linarith
  · have := le_max_right C₁ C₂
    linarith

end GlobalTheory.CompanionTheory.Ar.Ht.FlatLine

open GlobalTheory.CompanionTheory.Ar.Ht.FlatLine in

theorem GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  intro K _ ι _ Ω _ y d hAr hB A k u c hS hk hG hV
  obtain ⟨C, hC⟩ := exists_arch_bound hAr hB hS hV
  refine ⟨(c + C) / k, fun L _ _ w hw => ?_⟩
  obtain ⟨val, hv, hval⟩ := hG L w hw
  have hU := GlobalTheory.T.vertical_bound_height_compare K ι Ω y d hAr hB (fun b => k * A.a b) u c hV
    (fun z => (k : ℝ) * Real.log (A.h z)) L w hw val hv hval
  rw [ptHt_pow] at hU
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  set S := ∑ σ : L →+* ℂ, ((k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖) with hSdef
  have hSb : |S| ≤ (Module.finrank ℚ L : ℝ) * C := by
    calc |S| ≤ ∑ σ : L →+* ℂ, |(k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : L →+* ℂ, C := Finset.sum_le_sum fun σ _ =>
          hC _ (ptsOver_embed σ hw) _ ((map_ne_zero σ).2 hv) (hasVal_embed σ hval)
      _ = (Module.finrank ℚ L : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]
  have hm : |(Module.finrank ℚ L : ℝ)⁻¹ * S| ≤ C := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul_le_iff₀ hd]
    exact hSb
  have hT : |(k : ℝ) * lineHt A L w| ≤ c + C := by
    have := abs_sub_abs_le_abs_sub ((k : ℝ) * lineHt A L w) ((Module.finrank ℚ L : ℝ)⁻¹ * S)
    linarith
  rw [le_div_iff₀ hk']
  rwa [abs_mul, abs_of_pos hk', mul_comm] at hT
