import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgJetsRat

variable {D : D7} {N N' : ℕ}

theorem jet_embV_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (F : VC D N N' → ℂ) (hF : ContDiff ℂ ⊤ F)
    (hT : ∀ α, taylor D F α ∈ Qbar) {m : ℕ} (A : Fin m → Matrix (Fin N') (Fin N) D.host.E) :
    iteratedFDeriv ℂ m F 0 (fun j => embV D (tor0 D cc δ) (A j)) ∈ Qbar := by
  rw [GlobalTheory.JetTransport.mlin_expand]
  refine IntermediateField.sum_mem _ fun f _ => IntermediateField.mul_mem _ ?_ ?_
  · exact IntermediateField.prod_mem _ fun j _ => GlobalTheory.JetTransport.embT_mem _ _
  · rw [GlobalTheory.JetTransport.iFD_coord F hF f]
    refine IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun i _ => ?_) (hT _)
    exact IntermediateField.natCast_mem _ _

end GlobalTheory.AlgJetsRat

open GlobalTheory.AlgJetsRat in
theorem GlobalTheory.algJets_of_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  intro D cc δ δ₀ B N N' L L' F hδ hδ₀ hF hT g S e he hLa k ys hys
  have hc : ∀ j, ∃ (c : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E),
      c ∈ Qbar ∧ e.symm (δ₀⁻¹ • ys j) = c • embV D B.tor A := by
    intro j
    obtain ⟨s, hs, hsy⟩ := hys j
    have hx : e.symm ((s : ℂ) • ys j) ∈ La D B.tor L L' := (he _).1 (by simpa using hsy)
    obtain ⟨n, A, -, hA, -⟩ := hLa _ hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    refine ⟨δ / δ₀ * (s : ℂ)⁻¹, A, IntermediateField.mul_mem _ hδ
      (IntermediateField.inv_mem _ (IntermediateField.natCast_mem _ s)), ?_⟩
    have h1 : e.symm (ys j) = (s : ℂ)⁻¹ • (δ • embV D B.tor A) := by
      rw [← hA, map_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [map_smul, h1, smul_smul, smul_smul]
    congr 1
    field_simp
  choose c A hcQ hcA using hc
  show iteratedFDeriv ℂ k (F ∘ ((e.symm : (Fin g → ℂ) ≃L[ℂ] VC D N N') : (Fin g → ℂ) →L[ℂ] VC D N N')) 0
    (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, map_zero, hcA]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  exact IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun j _ => hcQ j)
    (jet_embV_mem cc δ F hF hT A)
