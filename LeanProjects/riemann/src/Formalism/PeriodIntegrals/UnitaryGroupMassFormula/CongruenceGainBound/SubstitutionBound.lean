import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Int

variable {σ τ Kc : Type} [Field Kc] (Oc : Subring Kc)

def IntP (x : MvPolynomial τ Kc) : Prop := ∀ m, MvPolynomial.coeff m x ∈ Oc

theorem coeffsIn_zero : IntP Oc (0 : MvPolynomial τ Kc) := fun m => by simp [Oc.zero_mem]

theorem coeffsIn_one : IntP Oc (1 : MvPolynomial τ Kc) := fun m => by
  classical
  rw [MvPolynomial.coeff_one]; split_ifs
  · exact Oc.one_mem
  · exact Oc.zero_mem

theorem coeffsIn_add {x y : MvPolynomial τ Kc} (hx : IntP Oc x) (hy : IntP Oc y) : IntP Oc (x + y) := fun m => by
  rw [MvPolynomial.coeff_add]; exact Oc.add_mem (hx m) (hy m)

theorem coeffsIn_mul₂ {x y : MvPolynomial τ Kc} (hx : IntP Oc x) (hy : IntP Oc y) : IntP Oc (x * y) := fun m => by
  classical
  rw [MvPolynomial.coeff_mul]
  exact Oc.sum_mem fun q _ => Oc.mul_mem (hx _) (hy _)

theorem coeffsIn_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial τ Kc) (h : ∀ i ∈ s, IntP Oc (f i)) :
    IntP Oc (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntP Oc) (fun _ _ => coeffsIn_add Oc) (coeffsIn_zero Oc) h

theorem IntA_zero : IntA Oc (0 : MvPowerSeries σ (MvPolynomial τ Kc)) := fun n => by
  simp only [map_zero]; exact coeffsIn_zero Oc

theorem IntA_one : IntA Oc (1 : MvPowerSeries σ (MvPolynomial τ Kc)) := fun n => by
  classical
  rw [MvPowerSeries.coeff_one]; split_ifs
  · exact coeffsIn_one Oc
  · exact coeffsIn_zero Oc

theorem IntA_add {F G : MvPowerSeries σ (MvPolynomial τ Kc)} (hF : IntA Oc F) (hG : IntA Oc G) :
    IntA Oc (F + G) := fun n => by
  rw [map_add]; exact coeffsIn_add Oc (hF n) (hG n)

theorem IntA_mul {F G : MvPowerSeries σ (MvPolynomial τ Kc)} (hF : IntA Oc F) (hG : IntA Oc G) :
    IntA Oc (F * G) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact coeffsIn_sum Oc _ _ fun q _ => coeffsIn_mul₂ Oc (hF _) (hG _)

end Int

end PI.UnitaryGroupMassFormula.PadicGainBound
