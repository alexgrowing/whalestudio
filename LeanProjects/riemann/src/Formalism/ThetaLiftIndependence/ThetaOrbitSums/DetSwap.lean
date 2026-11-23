import Formalism.ThetaLiftIndependence.Statement

namespace Formalism.ThetaLiftIndependence

namespace DeterminantSwapLemmas

variable {𝕜 E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

lemma mem_orth_ker_adjoint (T : E →ₗ[𝕜] F) (x : E) :
    T x ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← LinearMap.adjoint_inner_left, LinearMap.mem_ker.mp hu, inner_zero_left]

noncomputable def restr (T : E →ₗ[𝕜] F) :
    (LinearMap.ker T)ᗮ →ₗ[𝕜] (LinearMap.ker (LinearMap.adjoint T))ᗮ :=
  (T.comp (LinearMap.ker T)ᗮ.subtype).codRestrict _ (fun x => mem_orth_ker_adjoint T x)

lemma restr_apply (T : E →ₗ[𝕜] F) (x : (LinearMap.ker T)ᗮ) :
    ((restr T x : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T x := rfl

lemma restr_injective (T : E →ₗ[𝕜] F) : Function.Injective (restr T) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h0 : T x = 0 := by
    have := congrArg (fun y : (LinearMap.ker (LinearMap.adjoint T))ᗮ => (y : F)) hx
    simpa [restr_apply] using this
  have hk : (x : E) ∈ LinearMap.ker T := h0
  have hmem : (x : E) ∈ LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨hk, x.2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact Subtype.ext hmem

lemma finrank_orth_ker (T : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.ker T)ᗮ = Module.finrank 𝕜 (LinearMap.range T) := by
  have h1 := (LinearMap.ker T).finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  omega

lemma finrank_eq (T : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.ker T)ᗮ =
      Module.finrank 𝕜 (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
  rw [finrank_orth_ker, finrank_orth_ker, LinearMap.finrank_range_adjoint]

noncomputable def equiv (T : E →ₗ[𝕜] F) :
    (LinearMap.ker T)ᗮ ≃ₗ[𝕜] (LinearMap.ker (LinearMap.adjoint T))ᗮ :=
  LinearEquiv.ofBijective (restr T)
    ⟨restr_injective T,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq T)).mp
        (restr_injective T)⟩

lemma equiv_apply (T : E →ₗ[𝕜] F) (x : (LinearMap.ker T)ᗮ) :
    ((equiv T x : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T x := rfl

end DeterminantSwapLemmas

end Formalism.ThetaLiftIndependence
