import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTatePeriodFiltrationExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLubinTatePeriodElementStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK

theorem GlobalTheory.LTDegOne.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀, x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  intro l _ P AI hT K LL χ π z hLT τ₀
  obtain ⟨ω, t, u, hω0, hω2, ht, hg⟩ := GlobalTheory.T.exists_lubin_tate_period_element l K χ π z hLT
  obtain ⟨Ψ, hK, hG, h0, h1, h2⟩ := GlobalTheory.T.period_ring_embedding_properties l P AI hT K
  have hX1 : Ψ (toB K (ofA K ω)) ∈ (P.PD K).Fil 1 := h1 ω hω0
  have hX2 : Ψ (toB K (ofA K ω)) ∉ (P.PD K).Fil 2 := h2 ω hω0 hω2
  have hXU : Ψ (toB K (ofA K ω)) * Ψ u ∈ (P.PD K).Fil 1 := by
    simpa using (P.PD K).Fil_mul 1 0 _ _ hX1 (h0 u)
  have hXXU : Ψ (toB K (ofA K ω)) * (Ψ (toB K (ofA K ω)) * Ψ u) ∈ (P.PD K).Fil 2 := by
    simpa [one_add_one_eq_two] using (P.PD K).Fil_mul 1 1 _ _ hX1 hXU
  have hY : Ψ t = Ψ (toB K (ofA K ω)) + Ψ (toB K (ofA K ω)) * (Ψ (toB K (ofA K ω)) * Ψ u) := by
    rw [ht, map_mul, map_add, map_one, map_mul]; ring
  refine GlobalTheory.T.lubin_tate_period_filtration_exact l P K LL χ τ₀ (Ψ t) (fun g => ?_) ?_ ?_
  · rw [hG, hg, map_mul, hK]
  · rw [hY]
    exact add_mem hX1 ((P.PD K).Fil_anti 1 (by simpa [one_add_one_eq_two] using hXXU))
  · intro h
    apply hX2
    have := sub_mem h hXXU
    rwa [hY, add_sub_cancel_right] at this
