import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_level_of_embedding : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 → Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  first | exact @GlobalTheory.LevRestrict.finE_mem_congLev | exact GlobalTheory.LevRestrict.finE_mem_congLev | (intros; apply GlobalTheory.LevRestrict.finE_mem_congLev <;> assumption)
