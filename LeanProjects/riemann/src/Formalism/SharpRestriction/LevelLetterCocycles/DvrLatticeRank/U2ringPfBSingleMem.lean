import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.BlockProductRing
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section unitaryAbsoluteValueBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u2ringPfB_γ₀_comm (g h : W.Gam) (x : PowerSeries O) :
    W.γ₀ g (W.γ₀ h x) = W.γ₀ h (W.γ₀ g x) := by
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

theorem u2ringPfB_single_mem (c : ZMod n) (x : PowerSeries O) (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) :
    (Pi.single c x : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (Pi.single c x : LetA O n) = Pi.single c x
  intro δ hδ
  funext j
  show W.γ₀ δ ((Pi.single c x : LetA O n) j) = (Pi.single c x : LetA O n) j
  by_cases hj : j = c
  · subst hj
    simp only [Pi.single_eq_same]
    exact hx δ hδ
  · simp only [Pi.single_eq_of_ne hj, map_zero]

theorem u2ringPfB_letter_mem {a : LetA O n} (ha : a ∈ W.AΔ) (i : ZMod n) :
    ∀ δ ∈ W.DelF, W.γ₀ δ (a i) = a i := by
  intro δ hδ
  have h : W.γA δ a = a := ha δ hδ
  exact congrFun h i

theorem u2ringPfB_q₀_ne_zero [IsDomain O] [CharZero O] (hp : PD.p ≠ 0) : W.q₀ ≠ 0 := by
  intro h0
  have h := W.q₀_def
  rw [h0, mul_zero] at h
  have h1 := congrArg (PowerSeries.coeff 1) h.symm
  have e : ((1 + PowerSeries.X : PowerSeries O) ^ PD.p - 1) =
      ((((Polynomial.X + 1) ^ PD.p - 1 : Polynomial O)) : PowerSeries O) := by
    push_cast
    ring
  rw [e, Polynomial.coeff_coe, map_zero] at h1
  simp [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one, hp] at h1

end unitaryAbsoluteValueBounds

end Formalism.MainNotions.N.Ln34
