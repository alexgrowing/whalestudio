import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DenseHasCompactSupport

noncomputable section

namespace PositivityTheory.ThKOwn

open scoped SchwartzMap

theorem dense_compactSupport {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    Dense {f : 𝓢(V, ℂ) | HasCompactSupport (f : V → ℂ)} := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFunL
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e.symm
  have hPQ : ∀ f, P (Q f) = f := fun f => by ext x; simp [P, Q]
  have hr : DenseRange P := Function.Surjective.denseRange fun f => ⟨Q f, hPQ f⟩
  refine (hr.dense_image P.continuous (GlobalTheory.CompanionTheory.DiracComb.dense_hasCompactSupport _)).mono ?_
  rintro _ ⟨f, hf, rfl⟩
  exact HasCompactSupport.comp_homeomorph hf e.toHomeomorph

end PositivityTheory.ThKOwn

end
