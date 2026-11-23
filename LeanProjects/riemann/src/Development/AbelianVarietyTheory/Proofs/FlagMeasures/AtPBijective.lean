import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

def crd (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r :=
  pTop k r j q.2 * uEmb k r (upperIn β q.1)

abbrev Crd (ι : Type) (k r j : ℕ) (β : Fin r → ℕ) :=
  (UTin β → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) ×
    (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))

def atP {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) (v : ι) : (UTin β → ℂ) × PTop k r j :=
  (fun i => p.1 i v, fun a => p.2.1 a v, fun s => p.2.2.1 s v, fun a => p.2.2.2 a v)

def CC {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) : ι → Mat k r := fun v => crd k r j β (atP p v)

theorem usage₂ {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} :
    Function.Bijective (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun q => (fun i v => (q v).1 i, fun a v => (q v).2.1 a,
    fun s v => (q v).2.2.1 s, fun a v => (q v).2.2.2 a), fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.DegVol.RefCov
