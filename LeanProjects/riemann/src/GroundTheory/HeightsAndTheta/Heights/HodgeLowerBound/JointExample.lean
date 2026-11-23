import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjLineAmple
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

namespace Line

open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (phi sqSum)

def lineBW (t : ℝ) : CP 1 → ℝ :=
  cpBounded.regularised (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some t t cpEta

def lineMUFun (t : ℝ) (p q : ℕ) (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  Real.exp (lineBW t (projL z)) ^ q * (fsLine 2).h z ^ p

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

omit II hII in
theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

omit II hII in

def chartQ (k : Fin 2) (y : (Σ _ : Unit, Fin 2) → ℂ) : Fin 1 → ℂ :=
  fun j => (2 : ℂ)⁻¹ * (y ⟨(), k.succAbove j⟩ * (y ⟨(), k⟩)⁻¹)

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
