import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

theorem idemAt_mul_idem_add_conj {D : D7} {P Q' : Finset (Pl D.host.E)} (hP : SplitSet P) (hQ : Q' ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) (hPQ : PP ∉ Q') : idemAt PP * (idem Q' + cA D (idem Q')) = 0 := by
  rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_eq_zero fun q hq => hP.mul_eq_zero hPP (hQ hq) (fun e => hPQ (e ▸ hq)),
    Finset.sum_eq_zero fun q hq => hP.mul_conj hPP (hQ hq), add_zero]

set_option maxHeartbeats 6000000 in

theorem redFn_eq_one_of_suppAt : ∀ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {P Q' : Finset (Pl D.host.E)}, SplitSet P → Q' ⊆ P → ∀ {PP : Pl D.host.E}, PP ∈ P → PP ∉ Q' → ∀ {κ : GA D V}, Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ → redFn β PP (Lev.finE V κ) = 1 := by
  intro D V β P Q' hP hQ PP hPP hPQ κ hS hSupp
  obtain ⟨y, hy⟩ := hS
  obtain ⟨hint, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP (hP.isIdemAt hPP)
  have h0 := idemAt_mul_idem_add_conj hP hQ hPP hPQ

  have hk : ∀ i j, idemAt PP * (Formalism.L2.Theta.mt V κ - 1) i j = 0 := fun i j => by
    rw [← hSupp i j, ← mul_assoc, h0, zero_mul]
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl

  have hA : toEAf D (idemAt PP) • ((Lev.finE V κ).val - 1) = 0 := by
    ext i j
    have := congrArg (toEAf D) (hk i j)
    rw [RingHom.map_mul, RingHom.map_zero, Matrix.sub_apply, RingHom.map_sub] at this
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, hval, Matrix.map_apply, Matrix.zero_apply]
    convert this using 3
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hY : toEAf D (idemAt PP) • ((intGL D.host.F D.host.E _ y).val - 1) = 0 := by
    have hg : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V κ * β := by
      rw [← hy]; simp [frGL, MulAut.conj_apply, mul_assoc]
    have e1 : (intGL D.host.F D.host.E _ y).val - 1 = (β⁻¹).val * ((Lev.finE V κ).val - 1) * β.val := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul β⁻¹ β, inv_mul_cancel, Units.val_one,
        Units.val_mul, Units.val_mul]
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hy, redFn_frGL]
  ext i j
  have hij := congrFun (congrFun hY i) j
  have hsub : (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * y.val i j = (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    have hij' : toEAf D (idemAt PP) * ((intGL D.host.F D.host.E _ y).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) = 0 := by
      simpa only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply] using hij
    have h1ij : ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j : Lev.EAf D) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, h1ij, ← sub_eq_zero, ← mul_sub]
    exact hij'
  have := congrArg (resS D.host.F PP) hsub
  rw [RingHom.map_mul, RingHom.map_mul, h1, one_mul, one_mul] at this
  change (resS D.host.F PP) (y.val i j) = _
  rw [this, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.ExportSeries

end
