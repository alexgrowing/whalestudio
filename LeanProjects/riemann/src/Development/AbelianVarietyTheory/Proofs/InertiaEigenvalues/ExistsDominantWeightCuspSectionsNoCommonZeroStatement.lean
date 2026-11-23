import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDominantWeightCuspSectionsNoCommonZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom b m ∧ LastPos (T.Q.Dw j) b ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ m ∧ ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ P ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) b m), P k x ≠ 0 := by
  first | exact @GlobalTheory.BpfUniform.exists_weight_noCommonZero | exact GlobalTheory.BpfUniform.exists_weight_noCommonZero | (intros; apply GlobalTheory.BpfUniform.exists_weight_noCommonZero <;> assumption)
