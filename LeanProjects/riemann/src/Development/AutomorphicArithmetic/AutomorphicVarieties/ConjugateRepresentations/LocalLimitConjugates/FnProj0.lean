import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjectionAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CommOfZalg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.fnProj0 :
    UpperTheory.V.Cj.H.FnProj0 := by
  intro E _ _ _ a ha μ _ _ n e he c
  obtain ⟨P, Q, S, hP, hQ, hS, hres, hker, hlim⟩ := casimir_resolvent_projection E a ha μ n e he c
  obtain ⟨P', hP'⟩ := opLift E a ha μ P hP
  choose Q' hQ' using fun k => opLift E a ha μ (Q k) (hQ k)
  choose S' hS' using fun k => opLift E a ha μ (S k) (hS k)
  have hG := gardFacts E a ha μ
  obtain ⟨c1, c2, -, -⟩ := clFacts E a μ
  obtain ⟨-, -, hA⟩ := casOp E a n e he 0 c
  obtain ⟨hA1, hA2⟩ := hA (gard μ) fun X φ h => (hG φ h).2.2.2.1 X
  have hinj : ∀ φ ∈ gard μ, cl μ φ = 0 → φ = 0 := fun φ h h0 => c2 φ (hG φ h).1 (hG φ h).2.1 h0
  have hsub : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ - ψ) = cl μ φ - cl μ ψ := by
    intro φ hφ ψ hψ
    have h := (c1 φ ψ 1 (-1) (hG φ hφ).2.1 (hG ψ hψ).2.1).2
    simpa only [one_smul, neg_smul, sub_eq_add_neg] using h
  have oS := fun k => opComm E a ha μ (S k) (hS k) (S' k) (hS' k)
  refine ⟨P', Q', S', opComm E a ha μ P hP P' hP', fun k => opComm E a ha μ (Q k) (hQ k) (Q' k) (hQ' k), oS,
    fun k φ hφ => ?_, fun φ hφ => ?_, opLim E a ha μ Q P hQ hP hlim Q' P' hQ' hP'⟩
  · rw [hA2 (S' k) (oS k) φ hφ]
    have h1 := hQ' k φ hφ
    have h2 := hS' k _ (hA1 φ hφ)
    have h3 := (gard μ).sub_mem hφ h1.1
    refine sub_eq_zero.1 (hinj _ ((gard μ).sub_mem h3 h2.1) ?_)
    rw [hsub _ h3 _ h2.1, hsub _ hφ _ h1.1, h1.2, h2.2, hres k φ hφ, sub_self]
  · have h1 := hP' φ hφ
    have h2 := hA1 _ h1.1
    refine hinj _ h2 (inner_self_eq_zero (𝕜 := ℂ).1 ?_)
    rw [casSym E a ha μ n e c _ h1.1 _ h2, h1.2]
    exact hker _ _ h2
