import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjMaxRank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def multiprojPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e : ℕ} (R : AnLogRes P J e) (V : Set R.X) : LocPot V where
  U y := Subtype.val ⁻¹' R.U y.1
  isOpen_U y := (R.isOpen_U y.1).preimage continuous_subtype_val
  mem_U y := R.mem_U y.1
  φ y z := ∑ k, Real.log (∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)

def projPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e m : ℕ} (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ))
    (V : Set R.X) : LocPot V where
  U y := Subtype.val ⁻¹' R.U y.1
  isOpen_U y := (R.isOpen_U y.1).preimage continuous_subtype_val
  mem_U y := R.mem_U y.1
  φ y z := Real.log (∑ l, ‖Ψ (segre (R.lift y.1 z.1)) l‖ ^ 2)

def ProjPotMassEq.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ C : Set V, IsClopen C →
      mInt BV (fun _ => multiprojPot R V) (C.indicator fun _ => (1 : ℝ)) =
        mInt BV (fun _ => projPot R Ψ V) (C.indicator fun _ => (1 : ℝ))

end GroundTheory.Heights₂.Heights.Targets
