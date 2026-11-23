import Formalism.LocalToGlobal.CharacterGerms.UnitSeriesFrobenius
import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LMulP

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval

theorem pderiv_comm' {σ K : Type} [CommRing K] (i j : σ) (f : MvPowerSeries σ K) :
    pderiv K i (pderiv K j f) = pderiv K j (pderiv K i f) := by
  ext n
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases h : i = j
  · subst h; rfl
  · have e1 : ((n + Finsupp.single i 1 : σ →₀ ℕ) : σ → ℕ) j = n j := by
      simp [h]
    have e2 : ((n + Finsupp.single j 1 : σ →₀ ℕ) : σ → ℕ) i = n i := by
      simp [Ne.symm h]
    rw [add_right_comm n (Finsupp.single i 1), e1, e2]
    ring

section Law

variable {C : Type} [Field C] [CharZero C] {d : ℕ} (G : FGLaw C d)

def Mm (j k : Fin d) : PS C 1 d := ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), k) (G.F j))

end Law

section Alg

variable {C : Type} [Field C] {V : VF C}

end Alg

section Rec

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (Y : FBChart C V O d)

end Rec

end LMulP

end Formalism.L2.FormalSeriesBounds
