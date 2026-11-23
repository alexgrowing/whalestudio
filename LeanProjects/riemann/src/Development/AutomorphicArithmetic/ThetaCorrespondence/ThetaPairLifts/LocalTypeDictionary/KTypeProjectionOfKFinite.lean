import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimFrameStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteDimensionalSpanOfAdmissibleKType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimFrameStableStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.KTypeProj
theorem kType_projection_mem : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  intro hP D θ V S M hθ ψ hψ hcusp hWex b hpos hherm hKadj hLie
  obtain ⟨W, hWfd, hψW, hWK⟩ := hWex
  have hWK' : KStable θ M W := fun τ g hg f hf => hWK τ g hg.1 hg.2 f hf
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set F := typeSpan (rhoK θ M) (W ⊓ G) G with hFdef
  haveI hFfd : FiniteDimensional ℂ F := _root_.GlobalTheory.T.admissible_KType_span_finiteDimensional hP θ V S M hθ ψ hψ hcusp W hWfd hψW hWK' b hpos hherm hKadj hLie
  have hFG : F ≤ G := typeSpan_le _ _ _
  have hprojG : ∀ F' : Submodule ℂ (GA D V → ℂ), F' ≤ G → FiniteDimensional ℂ F' →
      ∃ π : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), (∀ x, π x ∈ F') ∧ ∀ x, ∀ f ∈ F', b (π x) f = b x f :=
    fun F' hF' hfd => GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim b F' hfd (fun x hx => hpos x (hF' hx)) (fun x hx y hy => hherm x (hF' hx) y (hF' hy))
  obtain ⟨e, heF, hechar⟩ := hprojG F hFG hFfd
  have hfix : ∀ f ∈ F, e f = f := by
    intro f hf
    by_contra hne
    have hd : e f - f ∈ F := F.sub_mem (heF f) hf
    have h0 : b (e f - f) (e f - f) = 0 := by
      rw [show b (e f - f) = b (e f) - b f from map_sub b _ _, LinearMap.sub_apply, hechar f _ hd, sub_self]
    have := hpos _ (hFG hd) (sub_ne_zero.2 hne)
    rw [h0] at this
    simp at this
  have hψF : ψ ∈ F := le_typeSpan _ inf_le_right ⟨hψW, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
  have hinvK : ∀ i : KIdx M, GlobalTheory.CuspGK.InK M i.1.1 i.1.2⁻¹ ∧ i.1.2⁻¹⁻¹ = i.1.2 := fun i => GlobalTheory.T.inMaxCompactOfModelFrame_inv M i.1.1 i.1.2 i.2
  let inv : KIdx M → KIdx M := fun i => ⟨(i.1.1, i.1.2⁻¹), (hinvK i).1⟩
  have hρG : ∀ i, ∀ x ∈ G, rhoK θ M i x ∈ G := (kStable_iff θ M G).1 (kStable_gkGen θ M ψ)
  have hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (rhoK θ M i x) y = b x (rhoK θ M (inv i) y) := by
    intro i x hx y hy
    have h := hKadj i.1.1 i.1.2⁻¹ (hinvK i).1 x hx y hy
    rw [(hinvK i).2] at h
    exact h.symm
  refine ⟨e, hfix ψ hψF, ?_, fun x _ => hfix _ (heF x), ?_, ?_⟩
  · intro A hAG hA x hx
    obtain ⟨Y, hYfd, hxY, hYK⟩ := GlobalTheory.T.kFinite_of_mem_gKModuleGeneratedBy θ M hθ ψ hψ ⟨W, hWfd, hψW, hWK'⟩ x (hAG hx)
    haveI := hYfd
    have hst := (kStable_iff θ M (Y ⊓ A)).1 (kStable_inf θ M hYK (kStable_of_isGKSub θ M hA))
    have := GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace b G (rhoK θ M) inv hpos hherm hρG hadj hprojG (W ⊓ G) e heF hechar (Y ⊓ A)
      inferInstance (inf_le_right.trans hAG) hst x ⟨hxY, hx⟩
    exact this.2
  · intro x hx y hy
    have h1 : b (e x) (y - e y) = 0 := by
      rw [← hherm _ (G.sub_mem hy (hFG (heF y))) _ (hFG (heF x)), map_sub, LinearMap.sub_apply,
        hechar y _ (heF x), sub_self, star_zero]
    have h2 : b (e x) y = b (e x) (e y) := by
      rw [map_sub] at h1
      exact sub_eq_zero.1 h1
    rw [h2, hechar x _ (heF y)]
  · refine Submodule.finiteDimensional_of_le (S₂ := F) ?_
    rintro _ ⟨x, -, rfl⟩
    exact heF x
end GlobalTheory.KTypeProj
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_projection_of_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  first | exact @_root_.GlobalTheory.KTypeProj.kType_projection_mem | exact _root_.GlobalTheory.KTypeProj.kType_projection_mem | (intros; apply _root_.GlobalTheory.KTypeProj.kType_projection_mem <;> assumption)
end
