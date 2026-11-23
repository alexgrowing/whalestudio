import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PureTensorExists

theorem existsUnique_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC x hx
  classical
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.PlaceTensor.base_std hB
  have hf0 : IsThetaFunO ψ S T f₀ := GlobalTheory.PlaceTensor.base_theta hB

  have build : ∀ (s : Finset (Place D)) (y : Place D → WO S T → ℂ),
      IsRestricted ψ θ S T sS sT ΛS ΛT f₀ y → (∀ p, y p ≠ f₀ → p ∈ s) →
        ∃ f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro y _ hy
      have hconst : y = fun _ => f₀ := by
        funext p
        by_contra hne
        exact absurd (hy p hne) (by simp)
      subst hconst
      exact ⟨f₀, (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1⟩
    · intro q s _ ih y hyR hy

      have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update y q f₀) := by
        refine ⟨fun p => ?_, ?_⟩
        · by_cases hpq : p = q
          · subst hpq
            simpa using GlobalTheory.PlaceTensor.base_isLocal hB p
          · simpa [Function.update_apply, hpq] using hyR.1 p
        · refine hyR.2.subset fun p hp => ?_
          by_cases hpq : p = q
          · subst hpq
            simp at hp
          · simpa [Function.update_apply, hpq] using hp
      have hsub : ∀ p, Function.update y q f₀ p ≠ f₀ → p ∈ s := by
        intro p hp
        by_cases hpq : p = q
        · subst hpq
          simp at hp
        · have hp' : y p ≠ f₀ := by simpa [Function.update_apply, hpq] using hp
          rcases Finset.mem_insert.1 (hy p hp') with h | h
          · exact absurd h hpq
          · exact h
      obtain ⟨f, hf⟩ := ih (Function.update y q f₀) hres hsub
      obtain ⟨f', hf', -⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC
        (Function.update y q f₀) y f q hf (by simp)
        (fun p hp => (Function.update_of_ne hp f₀ y).symm) (hyR.1 q)
      exact ⟨f', hf'⟩
  obtain ⟨f, hf⟩ := build hx.2.toFinset x hx (fun p hp => by simpa using hp)
  refine ⟨f, hf, fun g hg => ?_⟩

  obtain ⟨hHaar, hFD, -⟩ := id hC
  have hfT : IsThetaFunO ψ S T f := hf.2.1
  have hgT : IsThetaFunO ψ S T g := hg.2.1
  have hIP := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hstd hC
  have hd : IsThetaFunO ψ S T (g - f) := GlobalTheory.WeilVacMove.isTheta_sub hgT hfT
  have hz : g - f = 0 := by
    refine GlobalTheory.HeisTotal.eq_zero_of_orthogonal_translates D ψ hstd S T f₀ (g - f) hf0
      (GlobalTheory.PlaceTensor.base_ne_zero hB) hd μ 𝓕 hHaar hFD fun w => ?_
    have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₀ hf0
    have e1 : ipO μ 𝓕 g (heisO ψ S T w f₀) = ipO μ 𝓕 f (heisO ψ S T w f₀) := by
      rw [(hg.2.2 w).2, (hf.2.2 w).2]
    have e2 : ipO μ 𝓕 (heisO ψ S T w f₀) g = ipO μ 𝓕 (heisO ψ S T w f₀) f := by
      rw [(hIP g _ hgT hw).2.1, (hIP f _ hfT hw).2.1, e1]
    have e3 := ((hIP (g - f) _ hd hw).2.2.2.1 f hfT).2
    rw [sub_add_cancel] at e3
    have e4 : ipO μ 𝓕 (heisO ψ S T w f₀) (g - f) = 0 := by
      linear_combination e2 - e3
    exact e4
  exact sub_eq_zero.1 hz

end GlobalTheory.PureTensorExists
