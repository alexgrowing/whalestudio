import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem rep_conj_of_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  classical
  intro p _ D g ρ ρ' htr
  obtain ⟨φ, hφ, hspan⟩ := GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings p D
  haveI := D.freeO
  haveI := D.finO
  have hdim : Module.finrank ℂ ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) = Module.finrank ℤ D.O := by
    rw [Module.finrank_pi_fintype, D.rankO]
    simp [Module.finrank_matrix, NumberField.Embeddings.card]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ hspan hdim
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ' hspan hdim
  have key : ∀ (s : ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (f : (D.F →+* ℂ) → ℂ),
      (s (fun τ => Matrix.scalar (Fin D.m) (f τ))).trace = ∑ τ, f τ * (s (Pi.single τ 1)).trace := by
    intro s f
    have : (fun τ => Matrix.scalar (Fin D.m) (f τ)) = ∑ τ, f τ • (Pi.single τ 1 : (D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) := by
      ext τ i j
      simp [Finset.sum_apply, Pi.single_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    rw [this, map_sum, Matrix.trace_sum]
    simp [map_smul, Matrix.trace_smul]
  let χ : (D.F →+* ℂ) → (𝓞 D.F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro τ τ' h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
    ext x
    exact DFunLike.congr_fun h x
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp χ hχ
  rw [Fintype.linearIndependent_iff] at hlin
  have heq : ∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace := by
    have := hlin (fun τ => (σ (Pi.single τ 1)).trace - (σ' (Pi.single τ 1)).trace) (by
      funext c
      have h1 := htr c
      have hφ' : φ (algebraMap (𝓞 D.F) D.O c) = fun τ => Matrix.scalar (Fin D.m) (τ (c : D.F)) := funext (hφ c)
      rw [← hσ, ← hσ', hφ', key, key] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      simp only [χ, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [mul_comm] using h1)
    intro τ
    exact sub_eq_zero.mp (this τ)
  exact GlobalTheory.T.representations_equal_traces_conjugate (D.F →+* ℂ) D.m g D.m_pos σ σ' heq |>.imp fun h hh => ⟨hh.1, fun a => by rw [← hσ, ← hσ']; exact hh.2 _⟩

end GlobalTheory.UPel.HT
