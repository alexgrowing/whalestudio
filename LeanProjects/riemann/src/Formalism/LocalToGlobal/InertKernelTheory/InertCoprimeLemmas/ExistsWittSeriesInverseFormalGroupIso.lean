import Formalism.LocalToGlobal.InertKernelTheory.StatementBeCob
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeW
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeWInertOfSigma

noncomputable section

namespace Formalism.L2.KerInert.BeCob

open NumberField Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 At InertK ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.DworkPowerSeriesWeights (Integral)

theorem map_cob {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) :
    MvPowerSeries.map φ (cob F f) = cob (MvPowerSeries.map φ F) (PowerSeries.map φ f) := by
  unfold cob at1
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)),
    MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem cc_beLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (hb : BeRat g (eLT hLT))
    (hph : PowerSeries.constantCoeff g.ph = 0) : MvPowerSeries.constantCoeff (beLT hLT) = 0 := by
  have hex := hOk.2.2.1
  apply (k0ToC l).injective
  rw [map_zero, ← MvPowerSeries.constantCoeff_map]
  show MvPowerSeries.constantCoeff (MvPowerSeries.map (k0ToC l) (Formalism.L2.G.Pend.beOf g (eLT hLT))) = 0
  rw [Formalism.L2.G.Pend.map_beOf hb]
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (eLT hLT)⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    intro i
    rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hp0 := Formalism.MainNotions.J.cc_pt g hex (h0 0)
  have hp1 := Formalism.MainNotions.J.cc_pt g hex (h0 1)
  have hadd : MvPowerSeries.constantCoeff (g.add (g.pt (MvPowerSeries.C (eLT hLT)⁻¹ * MvPowerSeries.X 0))
      (g.pt (MvPowerSeries.C (eLT hLT)⁻¹ * MvPowerSeries.X 1)) : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    apply Formalism.MainNotions.J.cc_pt g hex
    rw [map_add, Formalism.MainNotions.J.cc_lg g hp0, Formalism.MainNotions.J.cc_lg g hp1, add_zero]
  unfold Formalism.L2.G.Pend.beC G1.be G1.phAt
  rw [map_sub, map_sub, PowerSeries.constantCoeff_subst_eq_zero hadd _ hph,
    PowerSeries.constantCoeff_subst_eq_zero hp0 _ hph, PowerSeries.constantCoeff_subst_eq_zero hp1 _ hph]
  simp

theorem simeq_neg {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {f g : MvPowerSeries ι K}
    (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : Formalism.InvariantFactorPaths.G7.Simeq (-f) (-g) := by
  have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.1 f g h
  unfold Formalism.InvariantFactorPaths.G7.Simeq at h' ⊢
  rwa [show -f - -g = g - f by ring]

theorem integral_X {K ι : Type} [NormedField K] (i : ι) : Integral (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem coboundary_equivalence : CobSimeq := by
  intro K _ _ _ F hF0 hFI f f' h
  have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit
  have hs : ∀ (φ : Unit → MvPowerSeries (Fin 2) K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      (∀ i, Integral (φ i)) →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst φ (f : MvPowerSeries Unit K))
        (MvPowerSeries.subst φ (f' : MvPowerSeries Unit K)) :=
    fun φ h0 hI => R.2.2.2.2 (Fin 2) f f' φ h0 hI h
  have h1 := hs (fun _ => F) (fun _ => hF0) (fun _ => hFI)
  have h2 := simeq_neg (hs (fun _ => MvPowerSeries.X 0) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have h3 := simeq_neg (hs (fun _ => MvPowerSeries.X 1) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have R2 := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)
  have H := R2.2.2.2.1 _ _ _ _ (R2.2.2.2.1 _ _ _ _ h1 h2) h3
  have e : ∀ q : PowerSeries K, cob F q = MvPowerSeries.subst (fun _ => F) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) := by
    intro q
    unfold cob at1 PowerSeries.subst
    ring
  rw [e f, e f']
  exact H

theorem lgF_eq_logF (l : ℕ) [Fact l.Prime] :
    PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
  rw [Formalism.L2.G.Pend.logF_map (p := l)]
  ext n
  unfold Formalism.MainNotions.GL3Theta.logF lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]

theorem cc_lgF' (K : Type) [Field K] (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [lgF]

theorem coboundary_exact : CobExact := by
  intro l _ g hLT hOk hb F hF
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' ℂ_[l] l
  have hlog0 : PowerSeries.constantCoeff (Formalism.MainNotions.FormalGroupSystem.logF l) = 0 := by
    have h1 : k0ToC l (PowerSeries.coeff 0 (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 := by
      rw [← PowerSeries.coeff_map, lgF_eq_logF, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact cc_lgF' ℂ_[l] l
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (map_eq_zero_iff _ (k0ToC l).injective).1 h1
  have hcK : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hlog0
  have hsK : MvPowerSeries.HasSubst (fun i : Fin 2 =>
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcK
  set c : Fin 2 → MvPowerSeries (Fin 2) ℂ_[l] := fun i => PowerSeries.subst (MvPowerSeries.X i) Lc with hcdef
  have hcC : ∀ i, MvPowerSeries.constantCoeff (c i) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hL0
  have hsC : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hcC
  have hB : MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) =
      MvPowerSeries.subst c (Formalism.L2.G.Pend.beC g e) := by
    unfold inParam
    rw [MvPowerSeries.map_subst hsK]
    have hc' : (fun i : Fin 2 => MvPowerSeries.map (k0ToC l)
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l))) = c := by
      funext i
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
        MvPowerSeries.map_X, lgF_eq_logF]
    rw [hc']
    congr 1
    exact Formalism.L2.G.Pend.map_beOf hb
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.C e⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    intro i
    rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  unfold Formalism.L2.G.Pend.beC at hB
  rw [Formalism.MainNotions.J.be_subst g hex hsC (Formalism.MainNotions.J.cc_pt g hex (h0 0)) (Formalism.MainNotions.J.cc_pt g hex (h0 1)),
    Formalism.MainNotions.J.pt_subst g hsC (h0 0), Formalism.MainNotions.J.pt_subst g hsC (h0 1), MvPowerSeries.subst_mul hsC,
    MvPowerSeries.subst_mul hsC, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsC, MvPowerSeries.subst_X hsC] at hB
  rw [hB]

  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hvS : PowerSeries.HasSubst (PowerSeries.C e⁻¹ * Lc) := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hcA : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.C e⁻¹ * c i) = 0 := by
    intro i; rw [map_mul, hcC i, mul_zero]
  have hat : ∀ i : Fin 2, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) (vLT hLT) =
      g.pt (MvPowerSeries.C e⁻¹ * c i) := by
    intro i
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply hvS
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]
    unfold G1.pt
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]
  have hpsi : ∀ i : Fin 2, at1 i (psiLT hLT) = g.phAt (g.pt (MvPowerSeries.C e⁻¹ * c i)) := by
    intro i
    unfold at1 psiLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), hat i]
    rfl
  have hlgA : ∀ i, g.lg (g.pt (MvPowerSeries.C e⁻¹ * c i)) = MvPowerSeries.C e⁻¹ * c i := by
    intro i
    unfold G1.lg G1.pt
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
      (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i)), hinv,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i))]
  set Fc := MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F with hFc
  have hFc0 : MvPowerSeries.constantCoeff Fc = 0 := by
    rw [hFc, MvPowerSeries.constantCoeff_map, hF.1, map_zero]
  have hLaw : PowerSeries.subst Fc Lc = c 0 + c 1 := by
    have h := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) hF.2.2
    rw [map_cob _ F hF.1, map_zero, Formalism.L2.Th1.E.Joints.map_lgF'] at h
    unfold cob at1 at h
    rw [← hFc] at h
    show _ = PowerSeries.subst (MvPowerSeries.X 0) Lc + PowerSeries.subst (MvPowerSeries.X 1) Lc
    linear_combination h
  have hadd : g.add (g.pt (MvPowerSeries.C e⁻¹ * c 0)) (g.pt (MvPowerSeries.C e⁻¹ * c 1)) =
      PowerSeries.subst Fc (vLT hLT) := by
    unfold G1.add
    rw [hlgA 0, hlgA 1, ← mul_add, ← hLaw]
    unfold vLT G1.pt
    rw [PowerSeries.subst_comp_subst_apply hvS (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hFc0), PowerSeries.subst_C]
  unfold G1.be cob
  rw [hadd, ← hpsi 0, ← hpsi 1]
  unfold G1.phAt psiLT
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
    (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]

theorem beta_coefficients : BeCoef := by
  intro l _ g hOk hM hph
  obtain ⟨P0, hP0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 hph
  obtain ⟨E0, hE0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 (Formalism.L2.G.Pend.exRat_of g hOk hM)
  obtain ⟨L0, hL0⟩ := Formalism.L2.G.Pend.l_mem_ratSub g hOk.2.1 hM
  have hP0' : PowerSeries.map (k0ToC l) P0 = g.ph := hP0
  have hE0' : PowerSeries.map (k0ToC l) E0 = g.ex := hE0
  have hL0' : PowerSeries.map (k0ToC l) L0 = g.l := hL0
  have hE00 : PowerSeries.constantCoeff E0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hE0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hOk.2.2.1
  have hL00 : PowerSeries.constantCoeff L0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hL0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.MainNotions.J.cc_l g
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hs0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero (hX 0) _ hL00,
      PowerSeries.constantCoeff_subst_eq_zero (hX 1) _ hL00, add_zero]
  have hs1 : MvPowerSeries.constantCoeff (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs0 _ hE00
  refine (Formalism.L2.G.Pend.coefWf_iff _).2 ⟨PowerSeries.subst (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) P0 -
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) P0 -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) P0, ?_⟩
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs1),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0), map_add,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    MvPowerSeries.map_X, MvPowerSeries.map_X, hP0', hE0', hL0']
  rfl

theorem X_mul_lU {K : Type} [Field K] [CharZero K] (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.X * Formalism.L2.Th1.B.lU f = f := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]

theorem integral_ps {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem phase_compatibility : PhTie := by
  intro l _ g hLT hOk s2 hph
  have hp : l.Prime := Fact.out
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' _ _
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  set v := vLT hLT with hvdef
  have hvcc : PowerSeries.constantCoeff v = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  set lW := Formalism.L2.Th1.A.logSer g.W with hlWdef
  have hgl : g.l = lW := Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff lW = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hlW1 : PowerSeries.coeff 1 lW = 1 := (Formalism.L2.Th1.A.logSpec ℂ_[l] g.W).2.1
  have hvl : PowerSeries.subst v lW = PowerSeries.C e⁻¹ * Lc := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  set P := Formalism.L2.Th1.A.wpReg g.W with hPdef
  have hP : Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)) = P := by
    rw [Sigma.wpReg_eq, hPdef, Sigma.wpReg_eq g.W, (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.1,
      (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.2.1]
  have hneg : ∀ f : PowerSeries ℂ_[l], PowerSeries.subst v (-f) = -PowerSeries.subst v f := fun f => by
    rw [← PowerSeries.coe_substAlgHom hvS, map_neg]
  have hlU1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hlW1]
  set U := PowerSeries.subst v (Formalism.L2.Th1.B.lU lW) with hU
  have hψ : psiLT hLT = -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog U := by
    unfold psiLT
    rw [hph]
    unfold Formalism.L2.Th1.B.phW Formalism.L2.Th1.B.phO
    rw [PowerSeries.subst_sub hvS, PowerSeries.subst_add hvS, hneg, PowerSeries.subst_mul hvS,
      PowerSeries.subst_pow hvS, PowerSeries.subst_C, hvl,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
    have hfl : PowerSeries.subst v (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU lW)) = Formalism.L2.Th1.B.fLog U := by
      rw [hU, PowerSeries.subst_def, PowerSeries.subst_def]
      exact Formalism.L2.Th1.B.subst_fLog (fun _ => hvcc) hlU1
    rw [← hfl]
    rfl
  have hFF : phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU Lc) := by
    unfold phFF
    rw [hP]

  have hvU : v * U = PowerSeries.C e⁻¹ * Lc := by
    have h1 : PowerSeries.subst v (PowerSeries.X * Formalism.L2.Th1.B.lU lW) = v * U := by
      rw [PowerSeries.subst_mul hvS, PowerSeries.subst_X hvS]
    rw [← h1, X_mul_lU lW hlW0, hvl]
  have hprod : Formalism.L2.Th1.B.lU Lc = (PowerSeries.C e * Formalism.L2.Th1.B.lU v) * U := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ_[l]))
    rw [X_mul_lU Lc hL0]
    calc Lc = PowerSeries.C e * (PowerSeries.C e⁻¹ * Lc) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hene, map_one, one_mul]
      _ = PowerSeries.C e * (v * U) := by rw [hvU]
      _ = PowerSeries.X * (PowerSeries.C e * Formalism.L2.Th1.B.lU v * U) := by
          rw [show PowerSeries.C e * (v * U) = PowerSeries.C e * ((PowerSeries.X * Formalism.L2.Th1.B.lU v) * U) by
            rw [X_mul_lU v hvcc]]
          ring

  have hex1 : PowerSeries.coeff 1 g.ex = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hinv
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hex, Formalism.L2.G.Pend.coeff_one_l g hOk.2.1, one_mul,
      PowerSeries.coeff_one_X] at h
    exact h
  have hv1 : PowerSeries.coeff 1 v = e⁻¹ := by
    rw [hvdef]
    unfold vLT
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hv0, hex1, one_mul, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hp.two_le, mul_one]
  have hA : MvPowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hv1, mul_inv_cancel₀ hene]
  have hLU : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU Lc) = 1 := Formalism.L2.Th1.E.Joints.cc_lU hp.two_le
  have hUc : MvPowerSeries.constantCoeff (U : MvPowerSeries Unit ℂ_[l]) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hprod
    rw [hLU, map_mul] at h
    have hA' : PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1 := hA
    rw [hA', one_mul] at h
    exact h.symm
  have hdiff : (psiLT hLT : MvPowerSeries Unit ℂ_[l]) -
      phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      Formalism.L2.Th1.B.fLog (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) := by
    rw [hψ, hFF, hprod, Formalism.L2.Th1.B.ParO.fLog_mul hA hUc]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdiff]; exact Formalism.L2.Th1.B.constantCoeff_fLog hA
  · rw [hdiff]
    show Integral (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog _))
    rw [Formalism.L2.Th1.B.fExp_fLog hA]
    apply integral_ps
    intro k
    rw [PowerSeries.coeff_C_mul, norm_mul, he1, one_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]
    exact v_integral hOk hLT (k + 1)

theorem norm_nat_one {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (m : ℕ) (hm1 : 0 < m) (hm : m < 5) :
    ‖(m : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  refine Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) ?_
  intro h
  have := Nat.le_of_dvd hm1 h
  omega

theorem thetaTie_of (hSI : ShortIso) : ThetaTie := by
  intro l _ h5 g hLT hOk n
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst (vLT hLT) := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  have hgl : g.l = Formalism.L2.Th1.A.logSer g.W := Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer g.W) = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hvl : PowerSeries.subst (vLT hLT) (Formalism.L2.Th1.A.logSer g.W) = PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one h5 2 (by norm_num) (by norm_num)
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one h5 3 (by norm_num) (by norm_num)
  have hiso := hSI ℂ_[l] h2 h3 g.W (Dict.intModel_of_ok hOk)
  have hθ : thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹ =
      MvPowerSeries.subst (fun _ => vLT hLT) (PowerSeries.subst (Formalism.L2.Th1.A.logSer g.W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)))) := by
    unfold thetaS
    rw [Formalism.L2.Th1.A.uSerEq ℂ_[l] _ _, ← PowerSeries.subst_def,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
  rw [hθ]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun _ => hvcc) (fun _ => integral_ps (v_integral hOk hLT)) hiso
    (Finsupp.single () n)

section IntPS

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem ips {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) (k : ℕ) :
    ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

theorem ips_add {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f + g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps; intro k
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips hf k) (ips hg k))

theorem ips_sub {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f - g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps; intro k
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips hf k) (by rw [norm_neg]; exact ips hg k))

theorem ips_Cmul {c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) :
    Integral ((PowerSeries.C c * f : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps; intro k
  rw [PowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (ips hf k)

theorem ips_X : Integral ((PowerSeries.X : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps; intro k
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem ips_mul {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f * g : PowerSeries K) : MvPowerSeries Unit K) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hf hg

end IntPS

theorem short_exact_isomorphism : ShortIso := by
  intro K _ _ _ h2 h3 W hW
  obtain ⟨hxI, hx1, hA, -⟩ := Formalism.L2.Th1.A.bridgeCurve K W hW
  obtain ⟨hB, -⟩ := Formalism.L2.Th1.A.bridgeCurve3 K W hW
  obtain ⟨hnum, hden⟩ := Formalism.L2.Th1.A.wpNumEq K W
  rw [← Formalism.L2.Th1.A.uSerEq K _ _]
  obtain ⟨hl0, hl1, -, -⟩ := Formalism.L2.Th1.A.logSpec K W
  have hlS : PowerSeries.HasSubst (Formalism.L2.Th1.A.logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hl_ne : Formalism.L2.Th1.A.logSer W ≠ 0 := by
    intro h; rw [h, map_zero] at hl1; exact zero_ne_one hl1
  set lW := Formalism.L2.Th1.A.logSer W with hlW
  set P := Formalism.L2.Th1.A.wpReg W with hP
  set xs := Formalism.L2.Th1.A.xS W with hxs
  set N : PowerSeries K := xs + PowerSeries.C (W.b₂ / 12) * PowerSeries.X ^ 2 with hN
  set D : PowerSeries K := xs - PowerSeries.C (W.a₁ / 2) * PowerSeries.X * xs -
    PowerSeries.C (W.a₃ / 2) * PowerSeries.X ^ 3 with hD
  have hD1 : PowerSeries.constantCoeff D = 1 := by
    rw [hD]; simp [hx1]
  have hden1 : PowerSeries.constantCoeff (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) ≠ 0 := by
    rw [hden]; simp

  have hsn : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 + lW ^ 2 * PowerSeries.subst lW P := by
    rw [hnum, PowerSeries.subst_add hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS,
      PowerSeries.subst_X hlS, ← PowerSeries.coe_substAlgHom hlS, map_one]
  have hsd : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P) := by
    rw [hden, PowerSeries.subst_sub hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_mul hlS,
      PowerSeries.subst_pow hlS, PowerSeries.subst_X hlS, PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom hlS,
      map_one]
    rfl
  set I := PowerSeries.subst lW (Formalism.L2.Th1.CM.uSer (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) with hI
  have hIB : I * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      lW * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) := by
    rw [hI, ← PowerSeries.subst_mul hlS]
    unfold Formalism.L2.Th1.CM.uSer
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hden1, mul_one, PowerSeries.subst_mul hlS, PowerSeries.subst_X hlS]
  rw [hsn, hsd] at hIB
  have hID : I * D = PowerSeries.X * N := by
    have h3ne : lW ^ 3 ≠ 0 := pow_ne_zero 3 hl_ne
    apply mul_left_cancel₀ h3ne
    have e2 : (2 : K) ≠ 0 := two_ne_zero
    have hB' : PowerSeries.X ^ 3 * (1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative K P)) =
        lW ^ 3 * D := by
      have hh : (PowerSeries.C (1 / 2 : K) : PowerSeries K) * (2 : PowerSeries K) = 1 := by
        rw [show (2 : PowerSeries K) = PowerSeries.C (2 : K) from (map_ofNat _ 2).symm, ← map_mul]; norm_num
      rw [hD]
      have ha1 : (PowerSeries.C (W.a₁ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₁ := by
        rw [← map_mul]; ring_nf
      have ha3 : (PowerSeries.C (W.a₃ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₃ := by
        rw [← map_mul]; ring_nf
      rw [ha1, ha3]
      linear_combination (-(PowerSeries.C (1 / 2 : K) : PowerSeries K)) * hB -
        (PowerSeries.X ^ 3 - lW ^ 3 * xs) * hh
    linear_combination PowerSeries.X ^ 3 * hIB - I * hB' + lW * PowerSeries.X * hA
  have hDinv : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel _ (by rw [hD1]; exact one_ne_zero)
  have hIe : I = PowerSeries.X * N * D⁻¹ := by
    calc I = I * D * D⁻¹ := by rw [mul_assoc, mul_comm D, hDinv, mul_one]
      _ = _ := by rw [hID]
  rw [hIe]

  have h12 : ‖(12 : K)‖ = 1 := by
    rw [show (12 : K) = 2 * 2 * 3 by norm_num, norm_mul, norm_mul, h2, h3]; norm_num
  have hi1 : ‖W.a₁‖ ≤ 1 := hW.1
  have hi2 : ‖W.a₂‖ ≤ 1 := hW.2.1
  have hi3 : ‖W.a₃‖ ≤ 1 := hW.2.2.1
  have hb2 : ‖W.b₂ / 12‖ ≤ 1 := by
    rw [norm_div, h12, div_one, WeierstrassCurve.b₂]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi1
    · rw [norm_mul]
      refine mul_le_one₀ ?_ (norm_nonneg _) hi2
      rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have ha12 : ‖W.a₁ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi1
  have ha32 : ‖W.a₃ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi3
  have hX2 : Integral (((PowerSeries.X : PowerSeries K) ^ 2 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_two]; exact ips_mul ips_X ips_X
  have hX3 : Integral (((PowerSeries.X : PowerSeries K) ^ 3 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_succ]; exact ips_mul hX2 ips_X
  have hNI : Integral ((N : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hN]; exact ips_add hxI (ips_Cmul hb2 hX2)
  have hDI : Integral ((D : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hD]
    exact ips_sub (ips_sub hxI (ips_mul (ips_Cmul ha12 ips_X) hxI)) (ips_Cmul ha32 hX3)
  have hDiI : Integral ((D⁻¹ : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hDI hD1 hDinv
  exact ips_mul (ips_mul ips_X hNI) hDiI

end Formalism.L2.KerInert.BeCob
