import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AveragingPreservesCuspType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormDecomposesIntoKFiniteComponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApproxStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
namespace GlobalTheory.CuspKFinDecomp
theorem cusp_average_k_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  intro D θ hθ hP N φ hφ U hU hlev e he l hl
  have key : ∀ l' : List D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) ∧
      (∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.CuspApproxAll.avgList θ N e l' φ (g * k) = GlobalTheory.CuspApproxAll.avgList θ N e l' φ g) ∧
      ∀ τ ∈ l', GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) := by
    intro l'
    induction l' with
    | nil => exact ⟨hφ, hlev, fun τ h => absurd h List.not_mem_nil⟩
    | cons τ l' ih =>
      rw [GlobalTheory.CuspApproxAll.avgList_cons]
      refine ⟨_root_.GlobalTheory.T.averaging_preserves_cusp_type D θ hθ hP N _ ih.1 τ (e τ) (he τ), avg_lev D θ hθ N _ U ih.2.1 τ (e τ), fun τ' hτ' => ?_⟩
      rcases List.mem_cons.1 hτ' with rfl | h
      · exact GlobalTheory.T.averaged_automorphic_function_K_finite D θ hθ N _ ih.1.1 τ' (e τ') (he τ')
      · exact GlobalTheory.T.average_preserves_K_finiteness D θ hθ N _ ih.1.1 τ' τ (e τ) (he τ) (ih.2.2 τ' h)
  obtain ⟨hc, hlv, hk⟩ := key l
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D N.V
    (Measure.haar : Measure (GA D N.V)) inferInstance
  obtain ⟨n, T₀, u, hT₀, hsum⟩ := _root_.GlobalTheory.T.cuspForm_decomposes_into_kFinite_components D θ hθ hP N _ hc U hU hlv (fun τ => hk τ (hl τ))
    (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕
  have hext := fun j => (GlobalTheory.GKExt.extExists hP.harishChandraModules hP.casselmanWallach D θ hθ N.V N.S N.M
    {k | k ∈ U ∧ k ∈ GfC N.V} 1 (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕 (T₀ j) (hT₀ j)).exists
  choose T hT using hext
  have hsm : ∀ τ (w : N.M.H τ), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → w ∈ N.M.sm τ := fun τ w hw =>
    (GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff N.M τ w).2 ((GlobalTheory.TypeSum.std_of_isDS hP.harishChandraModules (N.M.ds τ)).2.2.1 w hw)
  refine ⟨n, fun j => PiTensorProduct.lift (T j),
    fun j => PiTensorProduct.tprod ℂ (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)),
    fun j => ?_, fun j k hk hkf g => ?_, ?_⟩
  · exact N.multT_le_cusp θ {k | k ∈ U ∧ k ∈ GfC N.V} 1
      (Submodule.mem_map_of_mem (Submodule.subset_span (hT j).1))
  · rw [PiTensorProduct.lift.tprod]
    have := (hT j).1.lev (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)) k ⟨hk, hkf⟩ g
    simpa using this
  · rw [hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiTensorProduct.lift.tprod]
    exact ((hT j).2 _ (u j) fun τ => rfl).symm
end GlobalTheory.CuspKFinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  first | exact @_root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition | exact _root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition | (intros; apply _root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition <;> assumption)
end
