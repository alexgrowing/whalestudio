import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.AddPreservesExpCongruence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.PowMod

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Sub

variable {σ τ Kc : Type} [Field Kc] (Oc : Subring Kc)

def intSub : Subring (MvPowerSeries σ (MvPolynomial τ Kc)) where
  carrier := {F | IntA Oc F}
  mul_mem' := IntA_mul Oc
  one_mem' := IntA_one Oc
  add_mem' := IntA_add Oc
  zero_mem' := IntA_zero Oc
  neg_mem' := fun hF n m => by
    rw [map_neg, MvPolynomial.coeff_neg]; exact Oc.neg_mem (hF n m)

end Sub

section Low

variable {σ A : Type} [CommRing A]

def LowOrd (k : ℕ) (F : MvPowerSeries σ A) : Prop :=
  ∀ e : σ →₀ ℕ, e.degree < k → MvPowerSeries.coeff e F = 0

end Low

section Trunc

variable (Sh : Shape) {Kc : Type} [Field Kc]

end Trunc

section Trunc2

variable (Sh : Shape) {Kc : Type} [Field Kc]

def sT (p : ℕ) (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1) (D : ℕ) : MvPowerSeries Sh.ZV Kc :=
  ∑ l ∈ range (D + 1), MvPowerSeries.C ((-1 : Kc) ^ l) *
    MvPowerSeries.X (⟨v, (FormalGroupSystem.posSub e (2 * l), a, b)⟩ : Sh.ZV) ^ (p ^ (2 * l))

def sig (p : ℕ) (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1)
    (D : ℕ) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  ∑ l ∈ range (D + 1), MvPowerSeries.C (MvPolynomial.C ((-1 : Kc) ^ l)) *
    subV Sh Kc TT ⟨v, (FormalGroupSystem.posSub e (2 * l), a, b)⟩ ^ (p ^ (2 * l))

end Trunc2

section AgreeSum

variable {σ A : Type} [CommRing A]

theorem Agree.add {D : ℕ} {F F' G G' : MvPowerSeries σ A} (hF : Agree D F F') (hG : Agree D G G') :
    Agree D (F + G) (F' + G') := fun n hn => by rw [map_add, map_add, hF n hn, hG n hn]

end AgreeSum

end PI.UnitaryGroupMassFormula.PadicGainBound
