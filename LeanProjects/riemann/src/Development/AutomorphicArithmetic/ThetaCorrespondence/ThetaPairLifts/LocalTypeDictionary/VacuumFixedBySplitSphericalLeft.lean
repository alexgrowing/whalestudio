import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPlacesEmbedding
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVacuumHeckeEigenvalueEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPlacesEmbeddingStatement

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.SplitSphLeft
theorem vacuum_fixed_by_split_spherical_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hTr
  classical
  have hfin1 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F |
      ¬ G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    hTr.geo.hM.std
  have hfin2 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal}.Finite := by
    have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 hv
  have hfin3 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ⟨X.T ∪ hfin1.toFinset ∪ hfin2.toFinset ∪ hfin3.toFinset, ?_⟩
  intro v hv _ k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨⟨hvT, hstd⟩, hdiff⟩, h2⟩ := hv
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt
      (GlobalTheory.SplitSphLeft.isUnram_of_unramified' hTr.base.unram v) with hs | ⟨w, hw⟩
  · have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v hdiff
    obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM.vac v
    obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hTr v k hk.1 _ hSB
    have h1 := GlobalTheory.VacTransportLeft.transport_left F E σ B a a' G X om om' hTr v k hk θ hθ _ hSB φ₁ hφ₁ hvac hact
    obtain ⟨c, rfl⟩ := vac_unique_split_left F E σ B a a' G X om om' hTr v hs hψ θ hθ hvac φ₁ hφ₁ h1
    have hc := _root_.GlobalTheory.T.split_vacuum_hecke_eigenvalue_eq_one hPr F E σ B a a' G X om om' hTr v hs hvT hψ h2 hstd k hk c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hTr v w hw hvT k hk 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)
end GlobalTheory.SplitSphLeft
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_spherical_left_fixes_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  first | exact @_root_.GlobalTheory.SplitSphLeft.vacuum_fixed_by_split_spherical_left | exact _root_.GlobalTheory.SplitSphLeft.vacuum_fixed_by_split_spherical_left | (intros; apply _root_.GlobalTheory.SplitSphLeft.vacuum_fixed_by_split_spherical_left <;> assumption)
end
