import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

abbrev IncreasingRowChoicePerColumn (N : ℕ) (Y : YoungDiagram) : Type := ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N

def sig {Lt : Type} (N : ℕ) (s : Lt) : Fin N × Fin N → Lt × ℕ × Fin N := fun v => (s, (v.2 : ℕ), v.1)

theorem map_nablaX {Lt : Type} [Fintype Lt] (K : Type) [CommRing K] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : WeylLatticeDuality.ColChoice N nu) :
    map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rename (sig N s) (GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 p q
  simp [sig]

theorem colLen_le_of_rowLen {N : ℕ} {Y : YoungDiagram} (h : Y.rowLen N = 0) : Y.colLen 0 ≤ N := by
  by_contra hc'
  have hc := not_le.mp hc'
  have h1 : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr hc
  have h2 := YoungDiagram.mem_iff_lt_rowLen.mp h1
  omega

end GlobalTheory.WeylLatDualProof
