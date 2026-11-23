import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_embedding_stabilizer : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (c : ℕ) (ε : D.host.E), ε ≠ 0 → ∀ d : HermitianOrthogonalExtensionData A B c ε, ∃ ι : GA D A →* GA D B, (∀ h, ι h = stabilizerEmbedding d h) ∧ Continuous ι ∧ Function.Injective ι ∧ (∀ h, ι h ∈ GQ B ↔ h ∈ GQ A) ∧ (∀ h, ι h ∈ GfC B ↔ h ∈ GfC A) ∧ (∀ h, ι h ∈ GinfC B ↔ h ∈ GinfC A) ∧ (∀ g, g ∈ ι.range ↔ HMul.hMul (mt B g) (d.a.map (incA D)) = d.a.map (incA D)) ∧ (∀ h, HMul.hMul (mt B (ι h)) ((frameMat B A d.ι).map (incA D)) = HMul.hMul ((frameMat B A d.ι).map (incA D)) (mt A h)) ∧ ∀ τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∃ k' ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), ι (atTau θ A τ k) = atTau θ B τ k' := by
  first | exact @GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_hom_properties | exact GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_hom_properties | (intros; apply GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_hom_properties <;> assumption)
