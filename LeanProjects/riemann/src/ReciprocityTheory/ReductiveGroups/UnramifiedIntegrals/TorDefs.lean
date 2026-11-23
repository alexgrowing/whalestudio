import Mathlib
import Formalism.EllipticTorsion.FormalGroupPointsParametrisation
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementU
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

def InSub {C : Type} [Field C] (K : Subfield C) {W : WeierstrassCurve C} : W.toAffine.Point → Prop
  | .zero => True
  | .some x y _ => x ∈ K ∧ y ∈ K

def CoeffSub {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C) : Prop :=
  W.a₁ ∈ K ∧ W.a₂ ∈ K ∧ W.a₃ ∈ K ∧ W.a₄ ∈ K ∧ W.a₆ ∈ K

structure GoodPair (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ_[l]) : Prop where
  five : 5 ≤ l
  mem2 : g2 ∈ MaximalUnramifiedExtension l
  mem3 : g3 ∈ MaximalUnramifiedExtension l
  norm2 : ‖g2‖ ≤ 1
  norm3 : ‖g3‖ ≤ 1
  disc : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1

def TorPt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ∃ h : (shortW (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃)).toAffine.Nonsingular
          (lam ^ 2 * ι (L.weierstrassP z)) (lam ^ 3 * ι (L.derivWeierstrassP z) / 2),
        N • WeierstrassCurve.Affine.Point.some _ _ h = 0

end ReciprocityTheory.ChartRestriction.L1
