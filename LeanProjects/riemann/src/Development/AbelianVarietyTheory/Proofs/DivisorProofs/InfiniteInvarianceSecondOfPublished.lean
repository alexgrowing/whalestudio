import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFunctionStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenUnfoldingStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.InfB

theorem infInvB_of_hypotheses (hP : GlobalTheory.FunPr.Hypotheses₂) : InfInvB := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' ei' ev' hloc K hK X om om' om₁ om₁' hT hT₁ μK μ hμK hμ l hl
  have hlaw := GlobalTheory.T.config_b_local_eigen_triple hP F E σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁
  refine ⟨fun u hu hu' f => by rw [hlaw.1 u hu hu' f], fun g₀ g hL hg hg₀ f => ?_, fun g hg f => ?_⟩
  · rw [hlaw.2 1 g₀ g hL hg hg₀ f, GlobalTheory.ThK.InfB.fac_one, one_smul, hl g₀ hg₀]
  · have hex := GlobalTheory.T.weil_action_maps_schwartz hP F E σ (b + 2) (a + (b + 2)) G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil'
    have hpres : ∀ x, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), om' x Φ ∈ schA F _ :=
      fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
    have e1 : ∀ k : KAt K (evI F), (∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1)
        (locOpInf (om' (g, 1)) f) k.1 y.1) ∂μ) =
        GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f (k.1 * g) := by
      intro k
      simp only [GlobalTheory.ThK.InfB.coneFun, coneInfInt]
      rw [GlobalTheory.ThK.InfB.locOpInf_mul hex hpres k.2.2 hg f]
    simp_rw [e1]
    exact GlobalTheory.T.continuous_function_stabilizer_integral F E σ B b G.V' G₁.V' H 0 (b + 1) G.q (b + 2 - G.q) hT.base hT.geo.hV' hC.hH K hK μK hμK _
      (GlobalTheory.T.config_b_local_eigen_unfolding hP F E σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁ μ hμ l f)
      (GlobalTheory.T.config_b_local_eigen_triples hP F E σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁ μ hμ l hl f) g hg

end GlobalTheory.ThK.InfB

end
