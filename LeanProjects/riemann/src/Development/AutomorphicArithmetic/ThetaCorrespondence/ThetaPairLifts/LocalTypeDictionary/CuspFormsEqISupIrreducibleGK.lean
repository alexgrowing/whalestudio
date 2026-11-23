import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormPeterssonNonvanishingGelfandKirillov
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KTypeProjectionOfKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremumStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGK
variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)
theorem cuspForm_mem_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  intro hP D θ V S M hθ ψ hA hC hW
  obtain ⟨b, hpos, hherm, hK, hL⟩ := _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov hP θ V S M hθ ψ hA hC hW
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := _root_.GlobalTheory.T.kType_projection_of_kFinite hP θ V S M hθ ψ hA hC hW b hpos hherm hK hL
  refine GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector (IsGKSub θ M) (isGKSub_sInf θ M) (gkGen θ M ψ) (isGKSub_gkGen θ M ψ) b
    hpos hherm (fun A hAle hAP => ?_) e he2 he3 he4 he5 ψ (mem_gkGen θ M ψ) he1
  have hperp : ∀ f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a),
      f ∈ gkGen θ M ψ ∧ ∀ a ∈ A, b a f = 0 := fun f hf => by
    rw [Submodule.mem_inf] at hf
    exact ⟨hf.1, fun a ha => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf.2 a) ha)⟩
  have hmk : ∀ f, f ∈ gkGen θ M ψ → (∀ a ∈ A, b a f = 0) → f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
    fun f h1 h2 => Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun ha =>
      LinearMap.mem_ker.2 (h2 a ha)⟩
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).k τ g hg f hfN) fun a ha => ?_
    rw [hK τ g hg a (hAle ha) f hfN]
    exact hf0 _ (hAP.k τ g⁻¹ hg.inv a ha)
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).lie τ X hX f hfN) fun a ha => ?_
    rw [hL τ X hX a (hAle ha) f hfN, hf0 _ (hAP.lie τ X hX a ha), neg_zero]
end GlobalTheory.CuspGK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_eq_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  first | exact @_root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | exact _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | (intros; apply _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK <;> assumption)
end
