import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalEigenStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalEigenTriplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerHaarTripleStatement

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem coneInvA (hP : GlobalTheory.FunPr.Hypotheses₂) : ConeInvA := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg e he ei ev hloc K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ l hl g hg φ hφ
  obtain ⟨m, hm, hAe⟩ := GlobalTheory.T.config_a_local_eigen_stabilizer hP F E σ B b a' G G₁ H H' hcfg e he ei ev hloc K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have hφg := locOp_mem v (om (g, 1)) φ
  obtain ⟨hB1, hB2, hB3⟩ := GlobalTheory.T.config_a_local_eigen_triples hP F E σ B b a' G G₁ H H' hcfg e he ei ev hloc X om om' om₁ om₁' hT hT₁ v l hl φ hφ
  have hmem : ∀ (k : KAt K (evFin F v)) (t : idelesAt E (evFin F v)), (m t.1)⁻¹ * k.1 ∈ UAt σ G.V (evFin F v) :=
    fun k t => (UAtSub σ G.V (evFin F v)).mul_mem ((UAtSub σ G.V (evFin F v)).inv_mem (hm t.1 t.2).2) (mem_KAt.1 k.2).2
  rw [(hAe l _ hφg).2, (hAe l φ hφ).2]
  have e1 : ∀ (k : KAt K (evFin F v)) (t : idelesAt E (evFin F v)),
      coneEvFun B G H H' om v (ev v) l (locOp v (om (g, 1)) φ) ((m t.1)⁻¹ * k.1) =
        coneEvFun B G H H' om v (ev v) l φ ((m t.1)⁻¹ * k.1 * g) := fun k t => hB2 g hg _ (hmem k t)
  simp_rw [e1]
  refine GlobalTheory.T.config_a_stabilizer_haar_triple hP F E σ B b a' G G₁ H H' hcfg K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ m hm _ hB1 hB3
    (fun g' hg' => ?_) g hg
  have e2 : ∀ p : KAt K (evFin F v) × idelesAt E (evFin F v),
      coneEvFun B G H H' om v (ev v) l φ ((m p.2.1)⁻¹ * p.1.1 * g') =
        coneEvFun B G H H' om v (ev v) l (locOp v (om (g', 1)) φ) ((m p.2.1)⁻¹ * p.1.1) :=
    fun p => (hB2 g' hg' _ (hmem p.1 p.2)).symm
  simp_rw [e2]
  exact (hAe l _ (locOp_mem v (om (g', 1)) φ)).1

end GlobalTheory.ThK.LemF
