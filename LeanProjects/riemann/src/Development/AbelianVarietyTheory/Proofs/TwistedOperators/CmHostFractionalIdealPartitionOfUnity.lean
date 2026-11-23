import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAAPartition

theorem host_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    have h1 := D.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hc : D.host.ccE ≠ ⊥ := by
    unfold Formalism.BasicNotions.Host.ccE
    rw [Ne, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
    exact D.host.ccK_ne_bot
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb))

theorem host_AA_partition : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  intro D
  set I := D.host.AA with hI
  have hne : I ≠ 0 := host_AA_ne_zero D
  have h1 : (1 : D.host.E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hne]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ z ∈ I * I⁻¹, ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧
      (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => ∃ (m : ℕ) (a c : Fin m → D.host.E),
      (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧
        ∑ i, a i * c i = z) hz ?_ ?_
    · intro u hu v hv
      refine ⟨1, fun _ => u, fun _ => v, fun _ => hu, ?_, by simp⟩
      intro _ x hx
      have hvx : v * x ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hv hx
      rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_one_iff] at hvx
      obtain ⟨b, hb⟩ := hvx
      exact ⟨b, hb⟩
    · rintro u v ⟨m, a, c, ha, hc, rfl⟩ ⟨n, a', c', ha', hc', rfl⟩
      refine ⟨m + n, Fin.append a a', Fin.append c c', ?_, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using ha j
        · simpa using ha' j
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hc j
        · simpa using hc' j
      · rw [Fin.sum_univ_add]
        simp
  exact key 1 h1

end GlobalTheory.HostAAPartition
