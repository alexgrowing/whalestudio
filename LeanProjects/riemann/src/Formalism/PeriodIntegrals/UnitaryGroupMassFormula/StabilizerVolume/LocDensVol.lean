import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolC

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW PositiveNearLattice SdDualW VolAAW

theorem volAA_of (hC : CondAA) : VolAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ ψ hψ d b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1

  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  filter_upwards [hC F ψ hψ, ev_dual b σ hσσ J hJ.2 (a := a), ev_dualH b σ hσσ a]
    with v hv hL hH

  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : SecondCountableTopology (Fv F v) := by
    haveI : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨_, Set.countable_range (algebraMap F (Fv F v)),
        HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)⟩⟩
    exact UniformSpace.secondCountable_of_separable _
  constructor
  ·
    intro μv hμ
    have hA : ann (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))
        ((latSub b v a M : AddSubgroup _) : Set (Fin a → Fin M → Fv F v ⊗[F] E)) =
        (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
      ann_eq v (psiV F ψ v) (BR (Fv F v) σ J) (latV (M := M) (n := a) b v) hv
        (smul_latV b v σ J) hL
    exact vol_one_of_ann hμ
      (fun X T Y => by simp only [BR_add, psiV_add]) (latSub b v a M)
      (isCompact_latV b v a M) (isClopen_latV b v a M).isOpen hA
  ·
    intro νv hν
    have hA : ann (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T))
        (hermO b v σ a : Set (HermR (Fv F v) σ a)) = hermO b v σ a :=
      ann_eq v (psiV F ψ v) (pairHerm (Fv F v) σ a) _ hv (smul_hermO b v σ a) hH
    exact vol_one_of_ann hν
      (fun S T U => by simp only [pairHerm_add, psiV_add]) (hermO b v σ a)
      (isCompact_hermO b v σ a).1 (isCompact_hermO b v σ a).2 hA

end PI.VolStabS
