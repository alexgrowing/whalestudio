import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.HV

def vl (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) : ℝ := -Real.logb l ‖x‖

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ R : Type} [Group Γ] [CommRing R] [Algebra c.O R]

abbrev toBar (x : R →ₐ[c.O] c.O) : R →ₐ[c.O] PadicAlgCl l := (Algebra.ofId c.O (PadicAlgCl l)).comp x

structure PtHyp [IsLocalRing R] (η : Γ →* ℤˣ) (r : Γ →* GG 3 R) (x₀ : R →ₐ[c.O] c.O) : Prop where
  fixed : ∀ f : R →ₐ[c.O] PadicAlgCl l, IsLocPt f → Upper η (push f r) → Lower η (push f r) →
    push f r = push (toBar x₀) r
  rigid0 : ∀ j : ℤ, j ≤ 0 → RigidWt j r (toBar x₀)
  rigid : ∀ f : R →ₐ[c.O] PadicAlgCl l, TwoPt η r f → Rigid r f

end UpperTheory.V.U3
