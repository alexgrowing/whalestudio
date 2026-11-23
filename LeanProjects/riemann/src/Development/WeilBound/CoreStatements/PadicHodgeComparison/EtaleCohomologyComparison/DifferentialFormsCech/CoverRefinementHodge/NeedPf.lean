import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CovRefine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovOfLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om.Nt2

theorem cov_of_local' {O : Type} [CommRing O] {X : Scheme.{0}} (Q : X.Opens → Prop) (q : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated q] [QuasiCompact q] (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (Pb.Coord q V d)) :
    ∃ U : Pb.Cov q, ∀ α, Q (U.U α) :=
  _root_.UpperTheory.Reformulated.B.Qm13.cov_of_local Q q h

theorem cov_refine : CovRefine := by
  intro K _ X q _ _ _ κ V hV
  refine cov_of_local' (fun W => ∃ k, W ≤ V k) q fun x => ?_
  have hx : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, hWk⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V k) (x := x) hk
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ W le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hW le_top)
  obtain ⟨f, hf, hst⟩ :=
    GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hW h hxW
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨_, n, hf, ⟨k, fun y hy => hWk (X.basicOpen_le f hy)⟩, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hW f g hg he⟩

theorem pullH_id : PullHId := fun q h a n x => GlobalTheory.CompanionTheory.HodgePull.pullH_id _ _ q a n x

theorem pullC_id : PullCId := fun q h a j x => GlobalTheory.HodgeCoh.hodgePull_id q a j x

end CrystallineSemistableComparison.Om.Nt2
