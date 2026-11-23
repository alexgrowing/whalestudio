import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompSmulLatticeEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decomp_smul_lattice_embedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (x : GA D Y) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin V.rank → D.host.E), w ∈ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∃ y ∈ 𝔪 • latAt Λ x, ∃ u : 𝓞 D.host.E, u ∈ 𝔪 ∧ w = frameMat V Y d.ι *ᵥ y + (u : D.host.E) • zv d := by
  first | exact @GlobalTheory.UnitaryEmbeddingLattice.mem_smul_lattice_unitaryEmbedding | exact GlobalTheory.UnitaryEmbeddingLattice.mem_smul_lattice_unitaryEmbedding | (intros; apply GlobalTheory.UnitaryEmbeddingLattice.mem_smul_lattice_unitaryEmbedding <;> assumption)
