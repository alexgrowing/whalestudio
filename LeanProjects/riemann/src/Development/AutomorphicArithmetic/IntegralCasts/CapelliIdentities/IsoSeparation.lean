import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleProjectionExists

theorem UpperTheory.Reformulated.B.IsoSeparation.isoSep :
    ∀ {H M : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H] [inst_3 : AddCommGroup M]
      [inst_4 : _root_.Module ℂ M] {ρ : Representation ℂ H M} {Y : Submodule ℂ M} {σ : GlobalTheory.CuspRep.SmIrr H},
      UpperTheory.V.Hi.IsoSum ρ Y σ →
        ∀ {F : M},
          F ∈ Y →
            F ≠ (0 : M) →
              ∃ (p : M →ₗ[ℂ] σ.V),
                (∀ (g : H),
                    ∀ y ∈ Y,
                      (p : M → σ.V) (((ρ : H → M →ₗ[ℂ] M) g : M → M) y) =
                        ((σ.ρ : H → σ.V →ₗ[ℂ] σ.V) g : σ.V → σ.V) ((p : M → σ.V) y)) ∧
                  (p : M → σ.V) F ≠ (0 : σ.V) := by
  intro H M _ _ _ _ _ ρ Y σ h F hF h0
  cases σ with
  | mk V ρ' hs hi => exact UpperTheory.irreducible_projection_exists ρ' ρ hi Y h hF h0
