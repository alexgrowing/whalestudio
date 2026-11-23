import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c l : ℕ) (L : Fin c → ℕ) (_ : ∀ i, L (Fin.rev i) + L i = 2 * l) (S : Subgroup (GL (n ⊕ Fin c) k)) (_ : ∀ g : GL (n ⊕ Fin c) k, g ∈ S ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => l) L s ≤ Sum.elim (fun _ => l) L r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) (m : Measure S), m.IsHaarMeasure → m.IsMulRightInvariant := by
  first | exact @GlobalTheory.LevelUnimod.unimodular | exact GlobalTheory.LevelUnimod.unimodular | (intros; apply GlobalTheory.LevelUnimod.unimodular <;> assumption)
