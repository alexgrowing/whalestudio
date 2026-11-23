import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLatticeIffHat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_lattice_iff_hat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L : Set (Fin r → E)) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), IsSA G k →
    (IsKM (IsCMField.complexConj E) G L 1 k ↔ GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) L k) := by
  first | exact @GlobalTheory.KMStab.isKM_one_iff_stabHat_of_isSA | exact GlobalTheory.KMStab.isKM_one_iff_stabHat_of_isSA | (intros; apply GlobalTheory.KMStab.isKM_one_iff_stabHat_of_isSA <;> assumption)
