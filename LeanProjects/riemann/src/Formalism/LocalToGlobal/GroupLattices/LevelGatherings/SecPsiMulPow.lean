import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

class OrbSec (G : Type) [Group G] where
  sec : G → G → G
  sec_mem : ∀ z g, (sec z g)⁻¹ * g ∈ Subgroup.zpowers z
  sec_const : ∀ z g g', g⁻¹ * g' ∈ Subgroup.zpowers z → sec z g = sec z g'

section Generic

variable {G : Type} [Group G] [Finite G] [OrbSec G] (z : G)

def nOrb : ℕ := Nat.card (G ⧸ Subgroup.zpowers z)

def orbEquiv : Fin (nOrb z) ≃ G ⧸ Subgroup.zpowers z := (Finite.equivFin _).symm

def orbRep (v : Fin (nOrb z)) : G := OrbSec.sec z (Quotient.out (orbEquiv z v))

theorem orbRep_mk (v : Fin (nOrb z)) : (QuotientGroup.mk (orbRep z v) : G ⧸ Subgroup.zpowers z) = orbEquiv z v :=
  (QuotientGroup.eq.2 (OrbSec.sec_mem z _)).trans (QuotientGroup.out_eq' _)

theorem orbRep_of_mk (v : Fin (nOrb z)) (g : G) (h : (QuotientGroup.mk g : G ⧸ Subgroup.zpowers z) = orbEquiv z v) :
    orbRep z v = OrbSec.sec z g := by
  unfold orbRep
  apply OrbSec.sec_const
  apply QuotientGroup.eq.1
  rw [QuotientGroup.out_eq', h]

theorem posG_bij : Function.Bijective
    (fun x : (Σ _ : Fin (nOrb z), Fin (orderOf z)) => orbRep z x.1 * z ^ (x.2 : ℕ)) := by
  constructor
  · rintro ⟨v, s⟩ ⟨v', s'⟩ h
    simp only at h
    have hv : v = v' := by
      apply (orbEquiv z).injective
      rw [← orbRep_mk, ← orbRep_mk, QuotientGroup.eq]
      have : (orbRep z v)⁻¹ * orbRep z v' = z ^ (s : ℕ) * (z ^ (s' : ℕ))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← h, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers z _) (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z _))
    subst hv
    have hs : z ^ (s : ℕ) = z ^ (s' : ℕ) := mul_left_cancel h
    have : (s : ℕ) = s' := pow_injOn_Iio_orderOf (Set.mem_Iio.2 s.2) (Set.mem_Iio.2 s'.2) hs
    rw [Fin.ext this]
  · intro g
    classical
    set v := (orbEquiv z).symm (QuotientGroup.mk g) with hv
    have hmem : (orbRep z v)⁻¹ * g ∈ Subgroup.zpowers z := by
      rw [← QuotientGroup.eq, orbRep_mk, hv, Equiv.apply_symm_apply]
    rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hmem
    obtain ⟨k, hk, hkz⟩ := hmem
    refine ⟨⟨v, ⟨k, Finset.mem_range.1 hk⟩⟩, ?_⟩
    simp only
    rw [hkz, mul_inv_cancel_left]

def posG : (Σ _ : Fin (nOrb z), Fin (orderOf z)) ≃ G := Equiv.ofBijective _ (posG_bij z)

theorem posG_apply (v : Fin (nOrb z)) (s : Fin (orderOf z)) : posG z ⟨v, s⟩ = orbRep z v * z ^ (s : ℕ) := rfl

theorem posG_step (v : Fin (nOrb z)) (s : Fin (orderOf z)) : posG z ⟨v, posAdd s 1⟩ = posG z ⟨v, s⟩ * z := by
  rw [posG_apply, posG_apply, mul_assoc, ← pow_succ]
  congr 1
  simp only [posAdd]
  exact pow_mod_orderOf z _

theorem nOrb_mul_order : nOrb z * orderOf z = Nat.card G := by
  unfold nOrb
  rw [← Nat.card_zpowers, mul_comm]
  exact (Subgroup.zpowers z).card_mul_index

end Generic

open Formalism.FrobeniusOrbits Formalism.BasicNotions

theorem iotaH_nsmul (φ : Formalism.HC.Frame) (h : φ.A) (i : ℕ) : φ.iota (i • h) = φ.iota h ^ i := by
  induction i with
  | zero => simp [Formalism.HC.Frame.iota_zero]
  | succ n ih => rw [succ_nsmul, Formalism.HC.Frame.iota_add, ih]; exact (pow_succ _ _).symm

theorem bsC_add_nsmul {N : ℕ} [NeZero N] (h t : ZMod N) (i : ℕ) :
    Formalism.MainNotions.Inhab.bsC h (t + i • h) = Formalism.MainNotions.Inhab.bsC h t := by
  induction i with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ← add_assoc, Formalism.MainNotions.Inhab.bsC_step, ih]

theorem bsA_add_nsmul {φ : Formalism.HC.Frame} (h t : φ.A) (i : ℕ) :
    Formalism.MainNotions.Inhab.bsA h (t + i • h) = Formalism.MainNotions.Inhab.bsA h t := by
  induction i with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ← add_assoc, Formalism.MainNotions.Inhab.bsA_step, ih]

def secPsi (φ : Formalism.HC.Frame) (z g : φ.Psi) : φ.Psi :=
  ⟨((g : φ.GG).1, φ.iota (Formalism.MainNotions.Inhab.bsA (φ.iotaInv (z : φ.GG).2) (φ.iotaInv (g : φ.GG).2))),
    (Formalism.HC.Frame.mem_Psi_iff _).2 ((Formalism.HC.Frame.mem_Psi_iff _).1 g.2)⟩

theorem secPsi_mul_pow (φ : Formalism.HC.Frame) (z g : φ.Psi) (hz : (z : φ.GG).1 = 1) : ∃ i : ℕ, secPsi φ z g * z ^ i = g := by
  obtain ⟨i, hi⟩ := Formalism.MainNotions.Inhab.bsA_orb (φ.iotaInv (z : φ.GG).2) (φ.iotaInv (g : φ.GG).2)
  refine ⟨i, Subtype.ext (Prod.ext ?_ ?_)⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_pow, Prod.fst_mul, Prod.pow_fst, hz, one_pow, mul_one]
    rfl
  · simp only [Subgroup.coe_mul, Subgroup.coe_pow, Prod.snd_mul, Prod.pow_snd]
    show φ.iota _ * (z : φ.GG).2 ^ i = _
    conv_lhs => rw [← φ.iota_iotaInv (z : φ.GG).2]
    rw [Formalism.HC.Frame.iotaInv_iota, ← iotaH_nsmul, ← Formalism.HC.Frame.iota_add, hi, Formalism.HC.Frame.iota_iotaInv]

theorem secPsi_const (φ : Formalism.HC.Frame) (z g : φ.Psi) (hz : (z : φ.GG).1 = 1) (i : ℕ) : secPsi φ z (g * z ^ i) = secPsi φ z g := by
  have h1 : ((g * z ^ i : φ.Psi) : φ.GG).1 = (g : φ.GG).1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Prod.fst_mul, Prod.pow_fst, hz, one_pow, mul_one]
  have h2 : φ.iotaInv ((g * z ^ i : φ.Psi) : φ.GG).2 = φ.iotaInv (g : φ.GG).2 + i • φ.iotaInv (z : φ.GG).2 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Prod.snd_mul, Prod.pow_snd]
    conv_lhs => rw [← φ.iota_iotaInv (g : φ.GG).2, ← φ.iota_iotaInv (z : φ.GG).2, ← iotaH_nsmul, ← Formalism.HC.Frame.iota_add]
    rw [Formalism.HC.Frame.iotaInv_iota]
  apply Subtype.ext
  show (_, _) = (_, _)
  rw [h1, h2, bsA_add_nsmul]

open Classical in

instance orbSecPsi (φ : Formalism.HC.Frame) : OrbSec φ.Psi where
  sec z g := if (z : φ.GG).1 = 1 then secPsi φ z g else Quotient.out (QuotientGroup.mk g : φ.Psi ⧸ Subgroup.zpowers z)
  sec_mem z g := by
    by_cases hz : (z : φ.GG).1 = 1
    · rw [if_pos hz]
      obtain ⟨i, hi⟩ := secPsi_mul_pow φ z g hz
      have : (secPsi φ z g)⁻¹ * g = z ^ i := inv_mul_eq_of_eq_mul hi.symm
      rw [this]
      exact Subgroup.npow_mem_zpowers z i
    · rw [if_neg hz]
      exact QuotientGroup.eq.1 (Quotient.out_eq _)
  sec_const z g g' h := by
    by_cases hz : (z : φ.GG).1 = 1
    · rw [if_pos hz, if_pos hz]
      rw [← mem_powers_iff_mem_zpowers] at h
      obtain ⟨i, hi⟩ := h
      have hi' : z ^ i = g⁻¹ * g' := hi
      have : g' = g * z ^ i := by rw [hi', mul_inv_cancel_left]
      rw [this, secPsi_const φ z g hz]
    · rw [if_neg hz, if_neg hz, QuotientGroup.eq.2 h]

def zPsi (φ : Formalism.HC.Frame) (h : φ.MA) : φ.Psi := ⟨((1, 1), h), by rw [Formalism.HC.Frame.mem_Psi_iff]⟩

theorem zPsi_eq (φ : Formalism.HC.Frame) (h : φ.MA) : ((zPsi φ h : φ.Psi) : φ.GG) = ((c0, h) : φ.GG) * φ.cc := by
  simp [zPsi, Formalism.HC.Frame.cc, c0]

theorem orderOf_zPsi (φ : Formalism.HC.Frame) (h : φ.MA) : orderOf (zPsi φ h) = orderOf h := by
  rw [← Subgroup.orderOf_coe]
  have : ((zPsi φ h : φ.Psi) : φ.GG) = MonoidHom.inr G0 φ.MA h := rfl
  rw [this]
  exact orderOf_injective _ (fun a b hab => (Prod.ext_iff.1 hab).2) h

end Formalism.L2.G
