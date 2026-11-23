import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RtMemIsoTyp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsTypeLoc

theorem main : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  intro D M A hC i PI z F hF
  by_cases hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  · obtain ⟨L, -, hL⟩ := hC i
    rw [NTypes.onMt, dif_pos hz]
    rw [A.typeV, Submodule.mem_comap] at hF ⊢
    have e : (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) ⟨z, hz⟩ F) =
        actSum D L z ((M.loc i).real F) := hL ⟨z, hz⟩ F
    rw [e]
    unfold actSum Finsupp.sum
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (GlobalTheory.CenKeepsType.rt_mem_isoTyp _ _ _ _ hF)
  · rw [NTypes.onMt, dif_neg hz]
    exact Submodule.zero_mem _

end GlobalTheory.CenKeepsTypeLoc
