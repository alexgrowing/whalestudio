import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstant
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant : ∀ {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    (∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) →
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  first | exact @GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | exact GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | (intros; apply GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant <;> assumption)
