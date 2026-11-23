import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexiveStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairContragredientQuotientStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairDetTwistStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.ThetaLiftGL

theorem compactOpen_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem main : BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → HoweDualityGL →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t →
    IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π →
    π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  intro hBZ hB hH k _ _ _ _ r t μ V _ _ W _ _ σ π hrt hμs hμu hσs hσi hσu hπs hπi hθ
  have hb := compactOpen_basis k (r + t)
  have hIi : (prod₂ σ (detRep (Fin t) μ)).IsIrreducible :=
    BernsteinUnitaryProductIrreducible.prod₂_detRep hB t hσs hσi hσu hμs hμu
  have hIs : IsSmooth (prod₂ σ (detRep (Fin t) μ)) := isSmooth_prod₂ _ _
  have hπa : IsAdmissible π := (hBZ k).1 (Fin (r + t)) W π hπs hπi
  have hIa : IsAdmissible (prod₂ σ (detRep (Fin t) μ)) := (hBZ k).1 (Fin (r + t)) _ _ hIs hIi
  have hθI : ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) :=
    GlobalTheory.T.theta_pair_det_twist hBZ k r t μ V σ hrt hμs hμu hσs hσi hσu
  have hq : OmQuot μ σ (contra π) := GlobalTheory.T.theta_pair_contragredient_quotient k r (r + t) μ V W σ π hμs hπa hθ
  have hqI : OmQuot μ σ (contra (prod₂ σ (detRep (Fin t) μ))) :=
    GlobalTheory.T.theta_pair_contragredient_quotient k r (r + t) μ V _ σ _ hμs hIa hθI
  have hc := GlobalTheory.T.smoothContragredient_irreducible_and_reflexive (GL (Fin (r + t)) k) hb W _ π (prod₂ σ (detRep (Fin t) μ)) hπa hIa
  have hc' := GlobalTheory.T.smoothContragredient_irreducible_and_reflexive (GL (Fin (r + t)) k) hb _ W (prod₂ σ (detRep (Fin t) μ)) π hIa hπa
  obtain ⟨e⟩ := (hH k r (r + t) μ hμs).1 V _ _ σ (contra π) (contra (prod₂ σ (detRep (Fin t) μ)))
    hσs hσi (isSmooth_contra π) (hc.1 hπi) (isSmooth_contra _) (hc'.1 hIi) hq hqI
  exact hc.2.2 ⟨e⟩

end GlobalTheory.ThetaLiftGL
