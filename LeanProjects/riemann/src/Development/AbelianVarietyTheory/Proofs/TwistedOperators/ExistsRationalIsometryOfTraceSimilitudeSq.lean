import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometry
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.TraceSimilitude

theorem trace_natSq_mul {E : Type} [Field E] [NumberField E] (N : ℕ) (x : E) :
    Algebra.trace ℚ E ((N : E) ^ 2 * x) = (N : ℚ) ^ 2 * Algebra.trace ℚ E x := by
  have h : ((N : E) ^ 2) = algebraMap ℚ E ((N : ℚ) ^ 2) := by simp
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem exists_gl_of_trace_similitude : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  classical
  intro E _ _ _ r X X' N hN hn gam htr hsurj
  have hs : Submodule.span E (Set.range X.Λ.subtype) = ⊤ := by
    rw [← X.Λ_span]; congr 1; exact Subtype.range_coe
  have hs' : Submodule.span E (Set.range X'.Λ.subtype) = ⊤ := by
    rw [← X'.Λ_span]; congr 1; exact Subtype.range_coe
  obtain ⟨A, hA⟩ := FrameFibre.exists_matrix X.Λ.subtype X.Λ.injective_subtype hs
    (X'.Λ.subtype ∘ₗ gam)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := hA
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ∀ w : X'.Λ, (((N ^ 2) • w : X'.Λ) : Fin r → E) = ((N : E) ^ 2) • (w : Fin r → E) := by
    intro w
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul E]
    push_cast; rfl
  have hsurjA : Function.Surjective (Matrix.toLin' A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs', Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨((N : E) ^ 2)⁻¹ • (v : Fin r → E), ?_⟩
    rw [map_smul, Matrix.toLin'_apply, hA', hv, hcoe, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hN0), one_smul]
    rfl
  have hU : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.1 hsurjA
  set U := hU.unit with hUdef
  have hUA : (U : Matrix (Fin r) (Fin r) E) = A := hU.unit_spec
  let a : GL (Fin r) E :=
    ⟨(N : E)⁻¹ • A, (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hN0, one_smul, ← hUA, U.mul_inv],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hN0, one_smul, ← hUA, U.inv_mul]⟩
  have ha : (a : Matrix (Fin r) (Fin r) E) = (N : E)⁻¹ • A := rfl
  have hai : ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := rfl
  obtain ⟨ε, hε, hξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hn with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, _root_.one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have h1 : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ u v : X.Λ, herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      (N : E) ^ 2 * ε * herm X.Gm u v := by
    intro u v
    have h0 : -X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) -
        (N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v) = 0 := by
      refine FrameFibre.eq_zero_of_trace _ fun b => ?_
      have h2 := htr (b • u) v
      have h3 : ((b • u : X.Λ) : Fin r → E) = (b : E) • (u : Fin r → E) := rfl
      have h4 := FrameFibre.herm_smul_smul X'.Gm (b : E) 1 (A *ᵥ (u : Fin r → E))
        (A *ᵥ (v : Fin r → E))
      have h5 := FrameFibre.herm_smul_smul X.Gm (b : E) 1 (u : Fin r → E) (v : Fin r → E)
      rw [one_smul, h1, _root_.mul_one] at h4 h5
      rw [← hA', ← hA', h3, Matrix.mulVec_smul, h4, h5] at h2
      have e1 : (b : E) * (-X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) =
          -X'.ξ0 * ((b : E) * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) := by ring
      have e2 : (b : E) * ((N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v)) =
          (N : E) ^ 2 * (-X.ξ0 * ((b : E) * herm X.Gm u v)) := by ring
      rw [mul_sub, map_sub, e1, e2, trace_natSq_mul, h2, sub_self]
    rw [hξ] at h0
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * h0 -
      (X.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) * hε2
  have keyA : ∀ x y : Fin r → E, herm X'.Gm (A *ᵥ x) (A *ᵥ y) = (N : E) ^ 2 * ε * herm X.Gm x y := by
    intro x y
    obtain ⟨c, v, hc, hv⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs x
    obtain ⟨d, w, hd, hw⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs y
    have h2 := key v w
    rw [Submodule.subtype_apply] at hv hw
    rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, FrameFibre.herm_smul_smul,
      FrameFibre.herm_smul_smul] at h2
    have hc' : (c : E) ≠ 0 := by simpa using hc
    have hd' : cc (d : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)
    apply mul_left_cancel₀ (mul_ne_zero hc' hd')
    linear_combination h2
  refine ⟨a, ε, hε, hξ, fun v => ?_, fun w hw => ?_, fun x y => ?_⟩
  · rw [ha, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hN0, one_smul, hA']
  · obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have h3 : (U : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (N : E) ^ 2 • w := by
      rw [hUA, hA', hv, hcoe]
    have h2 : ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((N : E) ^ 2 • w) = v := by
      rw [← h3, Matrix.mulVec_mulVec, U.inv_mul, Matrix.one_mulVec]
    rw [hai, Matrix.smul_mulVec, smul_smul, ← pow_two, ← Matrix.mulVec_smul, h2]
    exact v.2
  · have hcc : cc ((N : E)⁻¹) = (N : E)⁻¹ :=
      (map_inv₀ (IsCMField.complexConj E) _).trans (by rw [map_natCast])
    rw [ha, Matrix.smul_mulVec, Matrix.smul_mulVec, FrameFibre.herm_smul_smul, hcc,
      keyA]
    field_simp

end GlobalTheory.TraceSimilitude
