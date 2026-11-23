import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZSeg GlobalTheory.SplitWeil GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.DerClass

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

noncomputable def iterLevi (n : ℕ) : (j : ℕ) → (GL (Fin n) k →* Mir k (n + j))
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (iterLevi n j)

abbrev dd (n j : ℕ) : Fin 2 → ℕ := ![n, j + 1]

theorem sum_dd (n j : ℕ) : ∑ a, dd n j a = n + j + 1 := by
  simp [dd, Fin.sum_univ_two, add_assoc]

abbrev ee (n j : ℕ) : (Σ a, Fin (dd n j a)) ≃ Fin (n + j + 1) := stdBlocks (dd n j) (sum_dd n j)

section Entries

variable {n j : ℕ} {g : GL (Fin (n + j + 1)) k}

end Entries

def blkF {n : ℕ} (g : Matrix (Fin n) (Fin n) k) (a b : ℕ) : k :=
  if h : a < n ∧ b < n then g ⟨a, h.1⟩ ⟨b, h.2⟩ else if a = b then 1 else 0

abbrev fstLevi (n j : ℕ) : GL (Fin (dd n j 0)) k →* Levi k fun a => Fin (dd n j a) :=
  MonoidHom.mulSingle (fun a => GL (Fin (dd n j a)) k) 0

end GlobalTheory.CompanionTheory.DerClass
