import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntegralHilbertNinety

theorem conj_sig (D : D7) : Formalism.L2.DIV.IsConjOf D.sp.cm.sig := by
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => ?_⟩
  · have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun e => (D.sp.cm.fixed e).1 (AlgHom.congr_fun h0 e)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩)).symm.trans (Module.finrank_self _)
    have := D.sp.cm.deg2
    omega
  · exact (D.sp.cm.fixed e).1 he

theorem swap_sig (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Lev.swapAE D (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig _ (Formalism.IndefR.Lev.swapAE D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

abbrev swapEquiv (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem swapEquiv_apply (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    swapEquiv D w = Formalism.IndefR.Lev.swapAE D w := rfl

set_option maxHeartbeats 2000000 in

theorem exists_int_unit_root : ∀ (D : D7) (z : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ),
    (z : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D →
    (∃ y₀ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
      z * sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E)) →
    ∃ y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  intro D z hz ⟨y₀, hy₀⟩
  have hss : ∀ w, sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig w) = w := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show a ⊗ₜ[D.host.F] (D.sp.cm.sig (D.sp.cm.sig x)) = a ⊗ₜ[D.host.F] x
      rw [(conj_sig D).2.1 x]
    | add a b ha hb => rw [map_add, map_add, ha, hb]

  have hzs : (z : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig z = 1 := by
    have h1 : sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
        sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      conv_lhs => rw [hy₀]
      rw [map_mul, hss]
    have h2 : (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      rw [mul_assoc, ← h1]; exact hy₀
    have h3 := congrArg (· * ((y₀⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E)) h2
    simp only [Units.mul_inv, mul_assoc, mul_one] at h3
    exact h3.symm
  have hzinv : ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig z := Units.inv_eq_of_mul_eq_one_right hzs

  obtain ⟨z', hz'⟩ : ∃ z' : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) = Formalism.IndefR.Lev.swapAE D z :=
    ⟨Units.map (Formalism.IndefR.Lev.swapAE D).toMonoidHom z, Units.coe_map _ _⟩
  have hconj : ∀ u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      ((Formalism.L2.DIV.conjId D.sp.cm.sig u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (u : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    intro u
    rw [Formalism.L2.DIV.conjId, Units.coe_map]
    rfl
  have hU1 : z' ∈ Formalism.L2.DIV.U1 D.sp.cm.sig := by
    rw [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hconj, hz', ← swap_sig, ← map_mul, hzs, map_one]
  have hz'inv : ((z'⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      Formalism.IndefR.Lev.swapAE D ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hz', ← map_mul, Units.mul_inv, map_one])
  have hint : z' ∈ Formalism.L2.DIV.intU D.host.F D.host.E := by
    rw [Formalism.L2.DIV.intU, Submonoid.mem_units_iff]
    refine ⟨?_, ?_⟩
    · rw [hz']
      exact (GlobalTheory.IdemSupport.mem_intAE_iff _).1 hz
    · rw [hz'inv]
      refine (GlobalTheory.IdemSupport.mem_intAE_iff _).1 ?_
      rw [hzinv]
      exact GlobalTheory.DetOnto.sigR_mem_intAE D hz
  obtain ⟨x, hx, hxz, -⟩ := GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial D.host.F D.host.E D.sp.cm.sig (conj_sig D)
    (GlobalTheory.HeckeAdjoint.unramified_host D) z' hU1 hint
  have hx' := (Submonoid.mem_units_iff _ _).1 hx
  have hxe : (x : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) * Formalism.UG.sigR D.sp.cm.sig _ (x : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    have h := congrArg (fun u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ =>
      ((u * Formalism.L2.DIV.conjId D.sp.cm.sig x : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) hxz
    simp only [Formalism.L2.DIV.h90, MonoidHom.div_apply, MonoidHom.id_apply, div_mul_cancel] at h
    rw [Units.val_mul, hconj] at h
    exact h
  refine ⟨Units.map (swapEquiv D).symm.toRingHom.toMonoidHom x, ?_, ?_, ?_⟩
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply]
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.1
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply, ← map_inv]
    change swapEquiv D ((swapEquiv D).symm ((x⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.2
  · apply (swapEquiv D).injective
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) =
      swapEquiv D ((z : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)))
    rw [RingEquiv.apply_symm_apply, map_mul, swapEquiv_apply, swapEquiv_apply, swap_sig, ← swapEquiv_apply D
      ((swapEquiv D).symm _), RingEquiv.apply_symm_apply, ← hz']
    exact hxe

end GlobalTheory.IntegralHilbertNinety
