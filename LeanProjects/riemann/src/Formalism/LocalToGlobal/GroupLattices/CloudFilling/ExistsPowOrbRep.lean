import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.SecPsiMulPow
import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

section Generic

variable {G : Type} [Group G] [Finite G] [OrbSec G] (z : G)

def orbOf (g : G) : Fin (nOrb z) := (orbEquiv z).symm (QuotientGroup.mk g)

theorem orbOf_mul_pow (g : G) (i : ℕ) : orbOf z (g * z ^ i) = orbOf z g := by
  unfold orbOf
  congr 1
  rw [QuotientGroup.eq]
  have : (g * z ^ i)⁻¹ * g = (z ^ i)⁻¹ := by group
  rw [this]
  exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z i)

theorem orbOf_orbRep (v : Fin (nOrb z)) : orbOf z (orbRep z v) = v := by
  unfold orbOf
  rw [orbRep_mk]
  exact (orbEquiv z).symm_apply_apply v

theorem orbOf_posG (v : Fin (nOrb z)) (s : Fin (orderOf z)) : orbOf z (posG z ⟨v, s⟩) = v := by
  rw [posG_apply, orbOf_mul_pow, orbOf_orbRep]

theorem exists_pow_orbRep (g : G) : ∃ i : ℕ, i < orderOf z ∧ orbRep z (orbOf z g) * z ^ i = g := by
  obtain ⟨⟨v, s⟩, hx⟩ := (posG z).surjective g
  refine ⟨s, s.isLt, ?_⟩
  rw [← hx, orbOf_posG]
  exact (posG_apply z v s).symm

end Generic

def tau1P (φ : Formalism.HC.Frame) (t : φ.A) : φ.Psi := ⟨φ.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩

abbrev zH (φ : Formalism.HC.Frame) (h : φ.A) : φ.Psi := zPsi φ (φ.iota h)

theorem tau1P_injective' (φ : Formalism.HC.Frame) : Function.Injective (tau1P φ) := by
  intro t t' h
  have h1 := congrArg (fun x : φ.Psi => ((x : φ.GG)).2) h
  simpa [tau1P, Formalism.HC.Frame.tau1, Formalism.HC.Frame.iota] using h1

theorem tau_add_nsmul (φ : Formalism.HC.Frame) (t h : φ.A) (i : ℕ) : tau1P φ (t + i • h) = tau1P φ t * zH φ h ^ i := by
  apply Subtype.ext
  have e1 : φ.iota (t + i • h) = φ.iota t * φ.iota h ^ i := by
    rw [← iotaH_nsmul]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  show (((1 : _), (1 : _)), φ.iota (t + i • h)) = (((1 : _), (1 : _)), φ.iota t) * (((1 : _), (1 : _)), φ.iota h) ^ i
  rw [e1]
  simp [Prod.pow_mk]

theorem orderOf_zH (φ : Formalism.HC.Frame) (h : φ.A) : orderOf (zH φ h) = addOrderOf h := by
  show orderOf (zPsi φ (φ.iota h)) = addOrderOf h
  rw [orderOf_zPsi]
  exact orderOf_ofAdd_eq_addOrderOf h

def vOfH (φ : Formalism.HC.Frame) (h t : φ.A) : Fin (nOrb (zH φ h)) := orbOf (zH φ h) (tau1P φ t)

def bsH (φ : Formalism.HC.Frame) (h t : φ.A) : φ.A :=
  φ.iotaInv ((orbRep (zH φ h) (vOfH φ h t) : φ.Psi) : φ.GG).2

private theorem orbRep_vOfH_eq_secPsi_tau1P (φ : Formalism.HC.Frame) (h t : φ.A) :
    orbRep (zH φ h) (vOfH φ h t) = secPsi φ (zH φ h) (tau1P φ t) := by
  have hv : (QuotientGroup.mk (tau1P φ t) : φ.Psi ⧸ Subgroup.zpowers (zH φ h)) =
      orbEquiv (zH φ h) (vOfH φ h t) :=
    ((orbEquiv (zH φ h)).apply_symm_apply _).symm
  have hz : ((zH φ h : φ.Psi) : φ.GG).1 = 1 := rfl
  have hs : OrbSec.sec (zH φ h) (tau1P φ t) = secPsi φ (zH φ h) (tau1P φ t) := if_pos hz
  rw [orbRep_of_mk _ _ _ hv, hs]

theorem bsH_eq_bsA (φ : Formalism.HC.Frame) (h t : φ.A) : bsH φ h t = Formalism.MainNotions.Inhab.bsA h t := by
  unfold bsH
  rw [orbRep_vOfH_eq_secPsi_tau1P]
  rfl

theorem vOfH_add_nsmul (φ : Formalism.HC.Frame) (h t : φ.A) (i : ℕ) : vOfH φ h (t + i • h) = vOfH φ h t := by
  unfold vOfH
  rw [tau_add_nsmul, orbOf_mul_pow]

theorem orbRep_vOfH (φ : Formalism.HC.Frame) (h t : φ.A) : orbRep (zH φ h) (vOfH φ h t) = tau1P φ (bsH φ h t) := by
  rw [orbRep_vOfH_eq_secPsi_tau1P, bsH_eq_bsA]
  exact Subtype.ext rfl

theorem bsH_orb' (φ : Formalism.HC.Frame) (h t : φ.A) : ∃ i : ℕ, i < addOrderOf h ∧ bsH φ h t + i • h = t := by
  obtain ⟨i, hi, he⟩ := exists_pow_orbRep (zH φ h) (tau1P φ t)
  refine ⟨i, by rwa [orderOf_zH] at hi, ?_⟩
  apply tau1P_injective' φ
  rw [tau_add_nsmul, ← orbRep_vOfH]
  exact he

theorem bsH_orb (φ : Formalism.HC.Frame) (h t : φ.A) : ∃ i : ℕ, bsH φ h t + i • h = t := by
  obtain ⟨i, -, hi⟩ := bsH_orb' φ h t
  exact ⟨i, hi⟩

theorem bsH_add_nsmul (φ : Formalism.HC.Frame) (h t : φ.A) (i : ℕ) : bsH φ h (t + i • h) = bsH φ h t := by
  unfold bsH
  rw [vOfH_add_nsmul]

theorem bsH_step (φ : Formalism.HC.Frame) (h t : φ.A) : bsH φ h (t + h) = bsH φ h t := by
  simpa using bsH_add_nsmul φ h t 1

theorem vOfH_bsH (φ : Formalism.HC.Frame) (h t : φ.A) : vOfH φ h (bsH φ h t) = vOfH φ h t := by
  obtain ⟨i, hi⟩ := bsH_orb φ h t
  rw [← vOfH_add_nsmul φ h (bsH φ h t) i, hi]

private theorem bsH_eq_of_vOfH_eq (φ : Formalism.HC.Frame) (h x y : φ.A) (hxy : vOfH φ h x = vOfH φ h y) :
    bsH φ h x = bsH φ h y := by
  unfold bsH
  rw [hxy]

theorem bsH_idem (φ : Formalism.HC.Frame) (h t : φ.A) : bsH φ h (bsH φ h t) = bsH φ h t := by
  exact bsH_eq_of_vOfH_eq φ h _ _ (vOfH_bsH φ h t)

theorem vOfH_injOn (φ : Formalism.HC.Frame) (h : φ.A) : Set.InjOn (vOfH φ h) (Set.range (bsH φ h)) := by
  rintro _ ⟨t1, rfl⟩ _ ⟨t2, rfl⟩ he
  calc bsH φ h t1 = bsH φ h (bsH φ h t1) := (bsH_idem φ h t1).symm
    _ = bsH φ h (bsH φ h t2) := bsH_eq_of_vOfH_eq φ h _ _ he
    _ = bsH φ h t2 := bsH_idem φ h t2

theorem posG_vOfH (φ : Formalism.HC.Frame) (h t : φ.A) (s : Fin (orderOf (zH φ h))) :
    posG (zH φ h) ⟨vOfH φ h t, s⟩ = tau1P φ (bsH φ h t + s.val • h) := by
  rw [posG_apply, orbRep_vOfH, tau_add_nsmul]

end Formalism.L2.G
