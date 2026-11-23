import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaVCases

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sig_nt (hcm : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  obtain ⟨-, htc, -, hst⟩ := hcm
  have hne : Nonempty (E →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := hne
  have hc := htc.isComplex (NumberField.InfinitePlace.mk φ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
  by_contra h
  push_neg at h
  apply hc
  ext x
  simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hx := hst φ x
  rw [h x] at hx
  rw [starRingEnd_apply]
  exact hx.symm

private theorem sc_of_isUnif_of_mem_integers {ϖ r : Fv F v} (hϖ : IsUnif v ϖ)
    (hr : r ∈ v.adicCompletionIntegers F) (hn : sc (E := E) v r ∉ PO (E := E) v ϖ) :
    r ≠ 0 ∧ r⁻¹ ∈ v.adicCompletionIntegers F := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hn ⟨0, Orb.oev_zero v, by simp [sc]⟩
  refine ⟨hr0, ?_⟩
  have hv0 : Valued.v r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0)]
  by_contra hlt
  push_neg at hlt
  apply hn
  have hle : Valued.v r ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    rw [WithZero.le_ofAdd_iff hv0]
    rw [← WithZero.coe_one, ← ofAdd_zero, WithZero.lt_ofAdd_iff hv0] at hlt
    omega
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    unfold IsUnif at hϖ
    simp at hϖ
  refine ⟨sc v (r * ϖ⁻¹), NormOneUnitFixedPoints.sc_mem v ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    unfold IsUnif at hϖ
    rw [hϖ]
    rw [mul_inv_le_iff₀ (zero_lt_iff.mpr (by simp)), one_mul]
    exact hle
  · rw [NormOneUnitFixedPoints.sc_mul_sc, mul_comm r, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]

theorem mem_of_theta (hcm : IsCMExt F E σ) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (θ : Fv F v ⊗[F] E)
    (hθ : θ ∈ OEv (E := E) v) (hnd : (θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ) ∉ PO (E := E) v ϖ)
    (z : Fv F v ⊗[F] E)
    (hz : ∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) :
    z ∈ OEv (E := E) v := by
  have hσσ := b_sig_sig σ hcm
  have htr := trace_v v σ hσσ (sig_nt σ hcm) hcm.2.2.1
  have hsθ := UnN.sigR_mem σ v hθ
  have hδ : θ - sigR (Fv F v) σ θ ∈ OEv (E := E) v := by
    rw [sub_eq_add_neg]
    exact Orb.oev_add v hθ (Orb.oev_neg v hsθ)
  have hfix : sigR (Fv F v) σ ((θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ))
      = (θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ) := by
    rw [map_mul, map_sub, sigR_sigR v σ hσσ θ]
    ring
  obtain ⟨r, hr, hreq⟩ := NormOneUnitFixedPoints.fix_int_sc σ v hcm (b_mul_mem v hδ hδ) hfix
  obtain ⟨hr0, hrinv⟩ := sc_of_isUnif_of_mem_integers v hϖ hr (hreq ▸ hnd)
  have ha := hz 1 (b_one_mem v)
  rw [one_mul] at ha
  have hb := hz θ hθ
  have key : (θ - sigR (Fv F v) σ θ) * z
      = algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (θ * z))
        - sigR (Fv F v) σ θ * algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) := by
    rw [htr, htr, map_mul]
    ring
  have hy : (θ - sigR (Fv F v) σ θ) * z ∈ OEv (E := E) v := by
    rw [key, sub_eq_add_neg]
    refine Orb.oev_add v ?_ (Orb.oev_neg v (b_mul_mem v hsθ ?_))
    · rw [← b_sc_eq]
      exact b_sc_mem v hb
    · rw [← b_sc_eq]
      exact b_sc_mem v ha
  have hz' : z = sc v r⁻¹ * ((θ - sigR (Fv F v) σ θ) * ((θ - sigR (Fv F v) σ θ) * z)) := by
    rw [← mul_assoc (θ - sigR (Fv F v) σ θ), hreq, ← mul_assoc, NormOneUnitFixedPoints.sc_mul_sc,
      inv_mul_cancel₀ hr0, NormOneUnitFixedPoints.sc_one, one_mul]
  rw [hz']
  exact b_mul_mem v (b_sc_mem v hrinv) (b_mul_mem v hδ hy)

private theorem exists_isUnif' : ∃ ϖ : Fv F v, IsUnif v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : Fv F v), ?_⟩
  unfold IsUnif
  rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  rfl

theorem trPerf_of_res (hR : Red.ResAlg σ J ψ v) : TrPerf σ J ψ v := by
  intro hstd hun z hz
  have hcm : IsCMExt F E σ := hstd.1
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif' v
  obtain ⟨θ, hθ, hnd⟩ := NormOneUnitFixedPoints.exists_theta σ J ψ v hR hstd hun hϖ
  exact mem_of_theta σ v hcm hϖ θ hθ hnd z hz

end PI.OmLocU.SdB
