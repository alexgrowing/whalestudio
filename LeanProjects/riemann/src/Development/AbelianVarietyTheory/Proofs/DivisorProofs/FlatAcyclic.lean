import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAdjointFibreOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatChernLogHessianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicSectionLaplacianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSectionPeriodicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelImagInverseIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicMetricSectionBoundStatement

set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
namespace GlobalTheory.TorsionForm.FlatAcyc

theorem flatAcyclic : FlatAcyclic := by
  intro E _ _ _ g B τ M j h hD hC b hb f hf hharm z I hI
  obtain ⟨hτ, hM, hj, hh⟩ := hD
  have hcov : ∀ z' : Fin g → ℂ, (b, z') ∈ cov B g := fun z' => ⟨hb, Set.mem_univ _⟩
  have hHs : ContDiff ℝ ∞ (fun z' : Fin g → ℂ => h (b, z')) :=
    hh.1.comp_contDiff (contDiff_prodMk_right b) hcov
  have hHpos : ∀ z' : Fin g → ℂ, 0 < h (b, z') := fun z' => hh.2.1 _ (hcov z')
  have hdiffh : ∀ z' : Fin g → ℂ, DifferentiableAt ℝ h (b, z') := fun z' =>
    (hh.1.contDiffAt ((hτ.1.prod isOpen_univ).mem_nhds (hcov z'))).differentiableAt (by simp)
  have hfd : Differentiable ℝ f := hf.1.differentiable (by simp)
  have h1 : ∀ z', fibreOp ((2 : ℂ) • imPart τ b) (fun z' => (Real.log (h (b, z')) : ℂ)) f z' = 0 :=
    fun z' => by rw [← GlobalTheory.T.dbar_adjoint_fibre_operator τ h b z' f hfd (hdiffh z') (hHpos z')]; exact hharm z'
  have hψs : ContDiff ℝ 2 (fun z' => (Real.log (h (b, z')) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hHs.log fun z' => (hHpos z').ne')).of_le (WithTop.coe_le_coe.2 le_top)
  have h3 := GlobalTheory.T.harmonic_section_laplacian _ _ (GlobalTheory.T.siegel_imag_inverse_identity (τ b) (hτ.2.2 b hb)) _ hψs
    (GlobalTheory.T.flat_chern_log_hessian hτ hh.1 hh.2.1 hC hb) f (hf.1.of_le (WithTop.coe_le_coe.2 le_top)) h1
  have hI' : (0 : ℝ) < I.card := by
    exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hI)
  refine GlobalTheory.T.periodic_metric_section_bound (τ b) (hτ.2.2 b hb) M hM (fun z' => h (b, z')) hHs hHpos
    (fun z' => f z' I) ((contDiff_apply ℝ ℂ I).comp hf.1) (fun l z' => j l (b, z')) ?_ ?_ ?_
    (2 * π * I.card) (by positivity) ?_ z
  · intro l hl z'
    have := congrFun (hf.2 l hl z') I
    simpa using this
  · intro l hl z' c
    exact GlobalTheory.T.dbar_section_periodicity hτ.1 hj hb f hf l hl z' c I
  · intro l hl z'
    exact hh.2.2 l hl (b, z') (hcov z')
  · intro z'
    have := h3 z' I
    push_cast
    exact this

end GlobalTheory.TorsionForm.FlatAcyc
