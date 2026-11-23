import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.L2.KerInert

open MvPowerSeries Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def BeWAt (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (g : G1 p) : Prop :=
  CoefWf (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    SimeqW (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    SimeqW (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2)) ∧
    ∀ α ∈ OKp D g.lam,
      SimeqW (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

def BePropOfBeW : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (g : G1 p)
    (hLT : LTIso g), At D cc δ g → 5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C → BeWAt D g →
    Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT)

def Adm2cAt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (g : G1 p)
    (hLT : LTIso g), At D cc δ g → 5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C → BeWAt D g →
    ∀ (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X), Y.be = beLT hLT → Formalism.MainNotions.FormalGroupSystem.adm2c D X Y

end Formalism.L2.KerInert
