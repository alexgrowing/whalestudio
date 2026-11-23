import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAverageHasType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AveragingPreservesCuspType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAverageHasTypeStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_kAverage : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  intro D θ hθ hp N U W _ _ _ ρ τ e he
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => GlobalTheory.Published.AutFin.conj_mem_UH hP hJ k
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have hA : ∀ f, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f =
      GlobalTheory.AvgOtherPlace.avgF θ N.V (muK (N.M.ε τ)) τ (fun k => (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ) e f := fun f => rfl
  refine ⟨GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun φ _ => GlobalTheory.SeriesToClosure.moves_avg hθ hP hJ hσ he φ⟩
  · intro f hf
    exact GlobalTheory.KFinAvgSpan.continuous_avg hθ hP hJ hec hf
  · intro f f' hf hf'
    rw [hA, hA, hA]
    exact GlobalTheory.AvgOtherPlace.avgF_add _ hθ hκ hU hec hf hf'
  · intro c f _
    rw [hA, hA]
    exact GlobalTheory.AvgOtherPlace.avgF_smul _ c f
  · intro f hf
    refine ⟨_root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType D θ hθ hp N f hf.1 τ e he, fun k hk hkf g => ?_⟩
    simp only [GlobalTheory.SeriesToClosure.avg]
    congr 1
    funext k'
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
      hf.2 k hk hkf]
  · intro τ' hne f hf hT x
    haveI := GlobalTheory.AvgCoeff.coeffSpan_finiteDimensional (ρ τ')
    have hAc : Continuous fun k' : KG (N.M.ε τ) => atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) :=
      GlobalTheory.RealAverage.continuous_atTau hθ hκ hU
    have hc : ∀ k k', GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k *
        atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) =
        atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k :=
      fun k k' => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ' τ hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k) _ (hU k')
    have hcont : ∀ k, Continuous fun k' : KG (N.M.ε τ) => e k' *
        f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) :=
      fun k => hec.mul (hf.1.1.cont.comp ((continuous_const.mul hAc).mul continuous_const))
    have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ)) (GlobalTheory.Published.AutFin.coeffSpan (ρ τ'))
      (fun k' k => e k' * f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) *
        GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k))
      (fun k' => Submodule.smul_mem _ (e k') (hT _)) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
    have heq : (fun k => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => ∫ k', e k' * f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) ∂(muK (N.M.ε τ)) := by
      funext k
      simp only [GlobalTheory.SeriesToClosure.avg]
      congr 1
      funext k'
      rw [mul_assoc, hc, ← mul_assoc]
    show (fun k => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) ∈ _
    rw [heq]
    exact key
  · intro τ' hne g hg f _
    funext x
    simp only [GlobalTheory.SeriesToClosure.avg, rTr]
    congr 1
    funext k
    rw [mul_assoc x, mul_assoc x, GlobalTheory.AvgOtherPlace.atTau_comm hθ hne (hU k) hg]
  · intro τ' hne X hX f hf
    rw [hA, hA]
    exact (GlobalTheory.AvgOtherPlace.avgF_Rder _ hθ hne hκ hU hec hf.1.1 hX).symm
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placewise_decomposition_of_K_average : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_kAverage
end
