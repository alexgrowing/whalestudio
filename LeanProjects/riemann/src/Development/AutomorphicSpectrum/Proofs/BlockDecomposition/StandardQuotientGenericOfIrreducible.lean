import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.StdIrrQuotGeneric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.CompanionTheory.BZSegQuot

theorem stdQuotGeneric_of_irr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.StdIrrQuotGeneric k → GlobalTheory.BZSeg.ProdIrrFiniteLength k →
    GlobalTheory.BZSeg.StdQuotGeneric k := by
  intro k _ _ _ _ hI hL h N Δ x hd hΔ ho W _ _ τ f hf hW
  have hs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth (isSmooth_prodIrr x hd)
  have hl : HasFiniteLength τ := IsFiniteLength.of_surjective (hL h N x hd)
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ τ f) hf
  obtain ⟨Y, _, _, τ', -, hi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient τ hs hl hW
  obtain ⟨ψ, hc, h1, hg⟩ := hI h N Δ x hd hΔ ho Y τ' (q.comp f) (hq.comp hf) hi
  refine ⟨ψ, hc, h1, nontrivial_twJacquet_of_surjective q.toLinearMap hq (fun u v => ?_) hg⟩
  refine Submodule.subset_span ⟨u, q v, ?_⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ (u : GL (Fin N) k) v)

end GlobalTheory.CompanionTheory.BZSegQuot

end
