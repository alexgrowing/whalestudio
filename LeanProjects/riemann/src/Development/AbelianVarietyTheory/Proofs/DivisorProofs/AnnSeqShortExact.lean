import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory.DualFlag

variable {X : Scheme.{0}} {S : ShortComplex X.Modules} {r s : ℕ}

theorem epi_dualMap_f (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) :
    Epi (dualMap S.f) := by
  classical
  refine QCoh.epi_of_locally_app_surjective _ fun W x hx => ?_
  obtain ⟨c, hc⟩ := VBExt.exists_adaptedChart hS h₁ h₃ x
  have hb := VBExt.isFrame_sumElim hS c.he c.ht
  refine ⟨c.U ⊓ W, ⟨hc, hx⟩, inf_le_right, fun l => ?_⟩
  refine ⟨∑ a : Fin r, dualApp l le_rfl (resM S.X₁ inf_le_left (c.e a)) •
    resM (dual S.X₂) inf_le_left (hb.coord (Sum.inl a)), ?_⟩
  refine c.he.dual_ext inf_le_left fun i => ?_
  rw [dualApp_dualMap, app_resM, dualApp_sum]
  simp only [LinearMap.sum_apply, dualApp_smul, dualApp_res, LinearMap.smul_apply]
  have e (a : Fin r) : dualApp (hb.coord (Sum.inl a)) (le_refl (c.U ⊓ W) |>.trans inf_le_left)
      (resM S.X₂ inf_le_left (S.f.app c.U (c.e i))) = if i = a then 1 else 0 := by
    have := hb.dualApp_coord_frame (Sum.inl a) (Sum.inl i) (inf_le_left : c.U ⊓ W ≤ c.U)
    simpa using this
  simp only [e, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, resG_self]

variable {E : X.Modules} {N : ℕ}

theorem shortExact_ι (fl : Vert.Flag E N) (i : Fin (N + 1)) :
    (ShortComplex.mk (fl.ι i) (cokernel.π _) (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

instance epi_dualMap_ι (fl : Vert.Flag E N) (i : Fin (N + 1)) : Epi (dualMap (fl.ι i)) :=
  epi_dualMap_f (S := .mk (fl.ι i) (cokernel.π _) (cokernel.condition _)) (r := i) (s := N - i)
    (shortExact_ι fl i) (fl.isVB i) (fl.isVB_cokernel i)

abbrev annSeq (fl : Vert.Flag E N) (i : Fin (N + 1)) : ShortComplex X.Modules :=
  .mk (kernel.ι (dualMap (fl.ι i))) (dualMap (fl.ι i)) (kernel.condition _)

theorem annSeq_shortExact (fl : Vert.Flag E N) (i : Fin (N + 1)) : (annSeq fl i).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }

theorem kernel_ι_comp_dualMap (fl : Vert.Flag E N) (k : Fin N) :
    kernel.ι (dualMap (fl.ι k.succ)) ≫ dualMap (fl.ι k.castSucc) = 0 := by
  rw [← fl.step_ι k, dualMap_comp, kernel.condition_assoc, zero_comp]

def dualFlag (fl : Vert.Flag E N) : Vert.Flag (dual E) N where
  F j := kernel (dualMap (fl.ι j.rev))
  ι j := kernel.ι _
  isSubbundle j := isSubbundle_of_shortExact (annSeq_shortExact fl j.rev) (fl.isVB j.rev).dual
  isVB j := by
    refine isVB_X₁_of_shortExact X _ j (N - j) (annSeq_shortExact fl j.rev) ?_ ?_
    · have := fl.isVB_self.dual
      rwa [show (j : ℕ) + (N - j) = N by omega]
    · have := (fl.isVB j.rev).dual
      rwa [Fin.val_rev, show N + 1 - ((j : ℕ) + 1) = N - j by omega] at this
  step j := kernel.lift _ (kernel.ι _) (by
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact kernel_ι_comp_dualMap fl j.rev)
  step_ι j := kernel.lift_ι _ _ _
  isIso_last := by
    have hz : IsZero (dual (fl.F (Fin.last N).rev)) := by
      refine isVB_zero_iff.1 ?_
      have := (fl.isVB (Fin.last N).rev).dual
      rw [Fin.rev_last] at this ⊢
      simpa using this
    rw [hz.eq_of_tgt (dualMap _) 0]
    infer_instance

end GlobalTheory.DualFlag
