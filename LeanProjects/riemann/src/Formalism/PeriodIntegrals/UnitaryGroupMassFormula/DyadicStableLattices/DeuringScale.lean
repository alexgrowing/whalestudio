import Formalism.PeriodIntegrals.GoodTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

def RootCubic : Prop :=
  ∀ j r : ℂ_[2], ‖j‖ ≤ 1 → (r + 16) ^ 3 = j * r → ‖r‖ ≤ 1

def UnitOfRoot : Prop :=
  ∀ j r : ℂ_[2], ‖r‖ = 1 → (r + 16) ^ 3 = j * r → ‖j‖ = 1

def UnitChoice : Prop :=
  ∀ d : ℕ, d % 8 = 7 → ∀ (h : ℕ) (x y : ℤ), 0 < h → Odd y →
    x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ π : ℂ, (π = x + y * omegaK d ∨ π = x + y * conj (omegaK d)) ∧ ‖ι π‖ = 1

def DeuringScale : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), W.Δ ≠ 0 →
    W.c₄ ^ 3 = ι (jInv L) * W.Δ →
    ∃ (c : ℂ) (hc : c ≠ 0), W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃

end PI.GoodTwo
