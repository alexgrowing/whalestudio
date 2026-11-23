import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatKernelFundamentalDomainPullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatKernelTraceIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrPullOperatorEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiPullBaseCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinDerivativeLinearCombStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.OneVec

open GlobalTheory.TorsionForm

theorem oneVector : OneVector := by
  intro E _ _ _ g n B τ M j h hD β a b hb T ⟨F, ⟨D, hFD, hK⟩, hM⟩
  refine ⟨pullBaseL a T, ⟨fun u => pullBaseL a (F u), ⟨D, hFD, fun u hu => ?_⟩, fun S => ?_⟩, ?_, ?_⟩
  · obtain ⟨K, hKK, hF⟩ := hK u hu
    refine ⟨fun t z z' => pullOp a (K t z z'), GlobalTheory.T.heat_kernel_fundamental_domain_pull hD β a hb u D hFD K hKK, ?_⟩
    simp only [GlobalTheory.T.str_pull_operator_eq]
    rw [ContinuousLinearMap.integral_comp_comm _
      (GlobalTheory.T.heat_kernel_trace_integrable β b u D hD.2.1 hFD K hKK), GlobalTheory.T.phi_pull_base_comm, hF]
  · show IsMellinDeriv (fun u => pullBase a (F u) S) (pullBase a T S)
    unfold pullBase
    split_ifs
    · exact hM ∅
    · exact GlobalTheory.T.mellin_derivative_linear_comb Finset.univ a (fun i u => F u {i.castAdd n}) (fun i => T {i.castAdd n})
        fun i _ => hM _
    · exact GlobalTheory.T.mellin_derivative_linear_comb Finset.univ (fun k => star (a k)) (fun k u => F u {k.natAdd n})
        (fun k => T {k.natAdd n}) fun i _ => hM _
    · have e : ∀ y : Ext (n + n), ∑ i, ∑ k, a i * star (a k) * y {i.castAdd n, k.natAdd n} =
          ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), (a p.1 * star (a p.2)) *
            y {p.1.castAdd n, p.2.natAdd n} := fun y => by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      have e' : (fun u => ∑ i, ∑ k, a i * star (a k) * F u {i.castAdd n, k.natAdd n}) =
          fun u => ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), (a p.1 * star (a p.2)) *
            F u {p.1.castAdd n, p.2.natAdd n} := funext fun u => e (F u)
      rw [e', e T]
      refine GlobalTheory.T.mellin_derivative_linear_comb (ι := Fin n × Fin n) _ _ (fun p u => F u {Fin.castAdd n p.1, Fin.natAdd n p.2}) (fun p => T {Fin.castAdd n p.1, Fin.natAdd n p.2}) ?_
      intro p _
      exact hM _
  · show pullBase a T ∅ = T ∅
    simp [pullBase]
  · show pullBase a T Finset.univ = _
    have h1 : (Finset.univ : Finset (Fin (1 + 1))) ≠ ∅ := Finset.univ_nonempty.ne_empty
    have h2 : (Finset.univ : Finset (Fin (1 + 1))) ≠ {Fin.castAdd 1 (0 : Fin 1)} := by
      intro h; have := Finset.mem_univ (Fin.natAdd 1 (0 : Fin 1)); rw [h] at this
      simp [Fin.ext_iff] at this
    have h3 : (Finset.univ : Finset (Fin (1 + 1))) ≠ {Fin.natAdd 1 (0 : Fin 1)} := by
      intro h; have := Finset.mem_univ (Fin.castAdd 1 (0 : Fin 1)); rw [h] at this
      simp [Fin.ext_iff] at this
    rw [pullBase, if_neg h1, if_neg h2, if_neg h3]

end GlobalTheory.TorsionForm.OneVec
