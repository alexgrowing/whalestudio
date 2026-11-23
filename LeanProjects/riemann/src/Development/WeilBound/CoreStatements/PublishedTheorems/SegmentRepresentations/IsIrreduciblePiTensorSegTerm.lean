import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.SegmentRepresentationLit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published

namespace PositivityTheory.Lit1.SegRep.PIrr

theorem isIrreducible_piTensor_segTerm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) :
    (piTensor (segTerm σ.ρ l)).IsIrreducible := by
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _
    (fun a => GlobalTheory.LocGL.isIrreducible_twist σ.irr _) fun a φ hφ => ?_
  refine GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id σ.ρ σ.smooth σ.irr φ fun g x => ?_
  have h := hφ g x
  simp only [segTerm, twist_apply, map_smul] at h
  exact (smul_right_injective _ (Units.ne_zero _)) h

end PositivityTheory.Lit1.SegRep.PIrr

end
