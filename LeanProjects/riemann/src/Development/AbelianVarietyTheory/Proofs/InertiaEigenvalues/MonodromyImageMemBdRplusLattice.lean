import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPowXiExtMemMan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinGaloisScalesDeRhamPeriodsByUnitPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.taylor_rho : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ v : OD l ↥(OL LL), IsUnit v ∧ ∀ w ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)), ∀ (R : ℕ) (j : ι), GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt w)) j - v ^ α * ∑ i ∈ Finset.range R, toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL)) * GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (w τ k))) j ∈ Ideal.span {GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ ^ R} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg
  obtain ⟨v, hv, hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg
  refine ⟨v, hv, fun w hw R j => ?_⟩
  exact taylor_vec (thetaW a LL) ϖ P α (descN_mem_Mext P) (E_pow_xiExt_mem_Man P α hα)
    (galOD ↥(OL LL) (sQ l g)) (rhoDHom T jD g) (rhoD_smul T jD g) (v ^ α)
    (GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg v hED)
    (fun i => toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL))) R _
    (fun f hf => GlobalTheory.T.taylor_formula_pi_invPrime_mod_eisenstein_pow l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg f hf R) hw j

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.key_sums (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (hl2 : l ≠ 2) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (hStd : IsStd Pl AI) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz (thetaW a LL) ϖ (sQ l) P jB) (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (hjD : ∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z)
    (α b : ℕ) (hα : ∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (ε : OCb l) (c : ℕ)
    (hk : ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k)) {m : Vec ↥LL.1 a ι} (hm : m ∈ P.M)
    {wx : Vec ↥LL.1 a ι} (hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e))) (hwxdef : P.xiExt wx = E ↥LL.1 l e ^ b • m) (j : ι)
    (k : ℕ) : ∑ i ∈ Finset.range (α + b), ((toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1) ^ i *
      Ring.inverse (i.factorial : OD l ↥(OL LL)) *
      YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
  have hgk : sQ l (g ^ k) ∈ GK (ϖ.field a) := by rw [map_pow]; exact Subgroup.pow_mem _ hg k
  obtain ⟨v, hv, htay⟩ := taylor_rho hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα (g ^ k) hgk
  have h1 := htay wx hwx (α + b) j
  obtain ⟨v', hv', hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l (g ^ k)) hgk
  have hxe : E ↥LL.1 l e ^ α • P.xiExt wx = E ↥LL.1 l e ^ (α + b) • m := by
    rw [hwxdef, smul_smul, ← pow_add]
  have h2 : rhoD T jD (g ^ k) (YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt wx)) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
    rw [hxe, YD_E_pow_smul (thetaW a LL) ϖ (P.M_le_Man hm) (α + b), rhoD_smul, Pi.smul_apply, smul_eq_mul, map_pow,
      hED, mul_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h3 : toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l (g ^ k))) = (toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1 := by
    rw [PiSys.mu, hk k, TensorProduct.tmul_sub, map_sub, ← Algebra.TensorProduct.one_def, map_one,
      ← pow_mul, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow, map_pow (WittVector.teichmuller l)]
  rw [h3] at h1
  have h4 := sub_mem h2 h1
  rw [sub_sub_cancel] at h4
  have h5 := Ideal.mul_mem_left _ (↑(hv.pow α).unit⁻¹ : OD l ↥(OL LL)) h4
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h5

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD m hm n hn w hw j
  obtain ⟨α, β₀, hα, hβ₀⟩ := P.exists_exponents
  have hβ : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.L := by
    have h1 := P.L.smul_mem (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) (hβ₀ m hm)
    have h2 : E ↥LL.1 l e ^ (β₀ + n) • m =
        (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) • E ↥LL.1 l e ^ β₀ • m := by
      rw [pow_add, mul_comm, mul_smul]
      rfl
    rw [h2]
    exact h1
  obtain ⟨g, ε, c, hε, hc, hg, hk⟩ := GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer l a e ϖ hl2
  obtain ⟨u, hu, hq⟩ := GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ε c hε hc
  obtain ⟨hnz, hnat⟩ := GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ
  have hxM : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.MMl := P.ext_mono (le_trans (A_le_S l e) (le_away _ _)) hβ
  have hsurj := P.xiExt.surjective (E ↥LL.1 l e ^ (β₀ + n) • m)
  obtain ⟨wx, hwxdef⟩ := hsurj
  have hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)) :=
    ((GlobalTheory.BK.xi_trivialises_invL_S ↥(OL LL) ↥LL.1 l e a ι P).2 wx).1 (by rw [hwxdef]; exact hxM)
  have hD1 := GlobalTheory.T.divided_difference_ideal_power_mem (OD l ↥(OL LL)) hnat (ED ↥LL.1 (thetaW a LL) ϖ) _ u hu hq (α + (β₀ + n))
    (fun i => YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j)
    (key_sums hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α (β₀ + n) hα g hg ε c hk hm hwx hwxdef j)
  have hfin := tail_step (thetaW a LL) ϖ P hnz (E_pow_xiExt_mem_Man P) (descN_mem_Mext P) α β₀ n hα hm hn hwx hwxdef j hD1
  rw [← iD_eq_YD (thetaW a LL) ϖ hn j (fun τ => w τ j) (fun τ => hw τ j)] at hfin
  exact hfin
