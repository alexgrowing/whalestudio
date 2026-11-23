import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.PHeisThC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate ContDiff

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem trace_fst_eq_zero (z : AE D) (hz : infPart D z = 0) :
    fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, fstA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).1 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_fst]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl
  rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

theorem trace_snd_eq_zero (z : AE D) (hz : finPart D z = 0) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, sndA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).2 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_snd]
    have : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl
  rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

variable (S T : HSp D)

set_option synthInstance.maxHeartbeats 400000 in
theorem infPart_hO (u w : MO S T) (hu : u.map (infPart D) = 0) : infPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, infPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO
  simp only [map_sum (infPart D), map_mul (infPart D), h0, mul_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_hO (u w : MO S T) (hu : u.map (finPart D) = 0) : finPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, finPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO
  simp only [map_sum (finPart D), map_mul (finPart D), h0, mul_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem symplO_fst_eq_zero (u w : MO S T) (hu : u.map (infPart D) = 0) : fstA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_fst_eq_zero _ ?_
  rw [map_mul (infPart D), infPart_hO S T u w hu, mul_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem symplO_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_snd_eq_zero _ ?_
  rw [map_mul (finPart D), finPart_hO S T u w hu, mul_zero]

theorem symplOH_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplOH S T u w) = 0 := by
  unfold symplOH
  rw [map_mul, symplO_snd_eq_zero S T u w hu, mul_zero]

def sndSympl (w : MO S T) : MO S T →+ Af D.host.F where
  toFun u := sndA D.host.F (symplO S T u w)
  map_zero' := by rw [symplO_zero_left, map_zero]
  map_add' u u' := by rw [symplO_add_left, map_add]

theorem heisStable : HeisStable D := by
  intro ψ hψ S T w f hf
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  obtain ⟨U, hUo, hU⟩ := hf.level
  let H : AddSubgroup (WO S T) := AddSubgroup.comap (sndSympl S T w) G
  have hHo : IsOpen (H : Set (WO S T)) :=
    hGo.preimage (continuous_snd.comp (cont_symplO_left S T w))
  refine ⟨fun γ z => ?_, ⟨U ⊓ H, ?_, fun u hu h0 => ?_⟩, cont_heis S T hψ hf w, fun k L hL hL0 x => ?_⟩
  ·
    unfold heisO
    rw [show ratW T S γ + z + w = ratW T S γ + (z + w) by abel, hf.quasi γ (z + w), ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    have key : symplOH S T (ratW T S γ + z) w + -symplOH S T (ratW T S γ) (z + w) =
        -symplOH S T (ratW T S γ) z + symplOH S T z w := by
      rw [symplOH_add_left, symplOH_add_right]; ring
    rw [key]
  · rw [AddSubgroup.coe_inf]; exact hUo.inter hHo
  ·
    have hfu := hU u hu.1 h0
    have hc : ψ (symplO S T u w) = 1 := by
      have e : symplO S T u w = pairA D.host.F 0 (sndA D.host.F (symplO S T u w)) := by
        refine Prod.ext ?_ rfl
        exact symplO_fst_eq_zero S T u w h0
      rw [e]; exact hG _ hu.2
    funext z
    have k1 := congrFun hfu (z + w)
    unfold heisO at k1 ⊢
    have hfz : f (z + w + u) = ψ (-(symplOH S T (z + w) u)) * f (z + w) := by
      rw [AddChar.map_neg_eq_inv, ← k1]; field_simp [psi_ne hψ]
    rw [show z + u + w = z + w + u by abel, hfz, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    have key : symplOH S T z u + symplOH S T (z + u) w + -symplOH S T (z + w) u =
        symplOH S T z w + symplO S T u w := by
      rw [symplOH_add_left, symplOH_add_left, symplOH_swap S T u w, ← symplOH_two]; ring
    rw [key, AddChar.map_add_eq_mul, hc, mul_one]
  ·
    let s : (Fin k → ℝ) →+ Ainf D.host.F :=
      { toFun := fun t => fstA D.host.F (symplOH S T (L t) w)
        map_zero' := by simp only [map_zero]; unfold symplOH; rw [symplO_zero_left, mul_zero, map_zero]
        map_add' := fun t t' => by simp only [map_add]; rw [symplOH_add_left, map_add] }
    have hs : Continuous s := continuous_fst.comp ((cont_symplOH_left S T w).comp hL)
    have e : (fun t => heisO ψ S T w f (x + L t)) =
        fun t => ψ (symplOH S T x w) * ψ (pairA D.host.F (s t) 0) * f (x + w + L t) := by
      funext t
      unfold heisO
      have ep : symplOH S T (L t) w = pairA D.host.F (s t) 0 :=
        Prod.ext rfl (symplOH_snd_eq_zero S T (L t) w (hL0 t))
      rw [symplOH_add_left, AddChar.map_add_eq_mul, ep, show x + L t + w = x + w + L t by abel]
    rw [e]
    exact (contDiff_const.mul (Formalism.IndefR.PHeisTh.psiSmooth D ψ hψ k s hs)).mul (hf.smooth k L hL hL0 (x + w))

theorem svnSchurO_all_of_heis (hK : KernelId D) (h : HeisStable D) : SvNSchurOAll D :=
  svnSchurO_all_of hK h

theorem svnSchurO_all_of_char (hC : CharComplete D) : SvNSchurOAll D :=
  svnSchurO_all_of_heis (kernelId_of hC) heisStable

end Formalism.IndefR.Fin

end
