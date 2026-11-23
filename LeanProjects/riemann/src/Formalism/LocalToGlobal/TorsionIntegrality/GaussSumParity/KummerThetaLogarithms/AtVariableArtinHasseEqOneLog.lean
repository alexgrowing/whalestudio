import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionPointsIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus oneLog thetaOne)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)

namespace SingleLetterLog

section Lin

variable {K : Type} [NormedField K] {τ : Type}

theorem iter_one (σ : K →+* K) (k : ℕ) : σ^[k] 1 = 1 :=
  Function.iterate_fixed (map_one σ) k

theorem univ_two : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

theorem linEL_two (σ : K →+* K) (L : ZMod 2 → MvPowerSeries τ K) : linEL σ 1 L = L 0 := by
  unfold linEL
  rw [univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1]

theorem linOL_two (σ : K →+* K) (L : ZMod 2 → MvPowerSeries τ K) : linOL σ 1 L = L 1 := by
  unfold linOL
  rw [univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1]

theorem trDual_two (σ : K →+* K) : TrDual 2 σ (fun _ : Unit => (1 : K)) (fun _ => 1) := by
  refine ⟨by simp, fun r r' => ?_⟩
  rw [univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1]

theorem owOK_two (σ : K →+* K) : OwOK 2 σ (fun _ : Unit => (1 : K)) (fun _ => 1) :=
  ⟨fun _ => ⟨by simp, by simp⟩, fun _ => ⟨iter_one σ 2, iter_one σ 2⟩⟩

end Lin

section Log

theorem at_variable_artin_hasse_eq_one_log {K τ : Type} [Field K] [DecidableEq τ] (l : ℕ) (x : τ) :
    at1 x (lgF K l) = oneLog l x := by
  ext n
  unfold at1
  rw [PowerSeries.coeff_subst_single]
  change _ = oneLog (K := K) l x n
  unfold oneLog lgF
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · have hd : n.degree = n x := by
      conv_lhs => rw [h]
      simp
    rw [hd]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h3 : (n = Finsupp.single x ((l ^ 2) ^ e)) ↔ n x = (l ^ 2) ^ e :=
      ⟨fun h' => by rw [h']; simp, fun h' => by rw [h, h']⟩
    simp only [h3]
  · symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp

end Log

end SingleLetterLog

open SingleLetterLog Pair

theorem OneLetterHalf_of : MeanSimeqL → OneLetterHalf := by
  intro hM K0 _ _ _ l σ hU F hF be0 hF1 hF2 ζ hζ ph hph
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hlK : (l : K0) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hrefl, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K0 Unit
  have hST : ShiftType l σ (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) :=
    fun _ => FormalExponential.ip_lgF l σ hl hlK
  have h1 := hM K0 l 2 σ hU le_rfl (by decide) F hF be0 hF1 hF2 Unit _ _ (owOK_two σ)
    (trDual_two σ) ζ hζ Unit _ hST
  have hX : constantCoeff (PowerSeries.X : MvPowerSeries Unit K0) = 0 :=
    PowerSeries.constantCoeff_X
  have hlog : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K0) (lgF K0 l) = lgF K0 l :=
    PowerSeries.X_subst _
  have h2 : subst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0))
      (beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1)) =
      subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0 := by
    rw [subst_tilde K0 l 2 σ hl be0 Unit _ _ Unit _ (fun _ => cc_lgF hl)]
    rw [Finset.univ_unique, Finset.sum_singleton, linEL_two, linOL_two]
    have h3 := addC_log exponential_specification hl hX hX be0
    rw [hlog] at h3
    rw [h3]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h2] at h1
  have h4 := B4.simeq_sub_zero (htrans _ _ _ hph (hsymm _ _ h1))
  have h5 := Formalism.InvariantFactorPaths.G7.Top.lamModule K0 Unit l σ hp hU.2.2.1 hU.2.2.2.2 _ 2
    (by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      have := hU.2.1
      omega) h4
  unfold Simeq at h5 ⊢
  have h2K : (2 : K0) ≠ 0 := two_ne_zero
  have e : ∀ B : MvPowerSeries Unit K0, (ph : MvPowerSeries Unit K0) - MvPowerSeries.C ((2 : K0)⁻¹) * B =
      MvPowerSeries.C (((2 : ℕ) : K0)⁻¹) * (MvPowerSeries.C (2 : K0) * ph - B) - 0 := by
    intro B
    rw [sub_zero, mul_sub, ← mul_assoc, ← map_mul]
    simp [h2K]
  rw [e]
  exact h5

theorem single_letter_of_half : OneLetterHalf → SingleLetterThetaFactorization := by
  intro hH K0 K _ _ _ _ _ _ l N0 N1 σ j hU hj F hF be0 hF1 hF2 ζ hζ ph hph U0 Φ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hU.1.two_le
  have h1 := hH K0 l σ hU F hF be0 hF1 hF2 ζ hζ ph hph
  generalize beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ = be at h1 ⊢
  have h2 := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K Unit j hj).1 _ _ h1
  have hsL0 : HasSubst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => cc_lgF hl)
  have hsL : HasSubst (fun _ : ZMod 2 => (lgF K l : MvPowerSeries Unit K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => cc_lgF hl)
  have e2 : MvPowerSeries.map j (MvPowerSeries.C ((2 : K0)⁻¹) *
      subst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) be) =
      MvPowerSeries.C ((2 : K)⁻¹) *
        subst (fun _ : ZMod 2 => (lgF K l : MvPowerSeries Unit K)) (MvPowerSeries.map j be) := by
    rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_subst hsL0, map_inv₀, map_ofNat]
    have e3 : MvPowerSeries.map j (lgF K0 l : MvPowerSeries Unit K0) = lgF K l :=
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF j l
    simp only [e3]
  rw [e2] at h2
  obtain ⟨-, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin N0 × Fin N1)
  have hsub := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit).2.2.2.2 (Fin N0 × Fin N1)
  have h3 : ∀ x : Fin N0 × Fin N1, Simeq (at1 x (PowerSeries.map j ph))
      (MvPowerSeries.C ((2 : K)⁻¹) *
        subst (fun _ : ZMod 2 => at1 x (lgF K l)) (MvPowerSeries.map j be)) := by
    intro x
    have hsx : HasSubst (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have h4 := hsub _ _ (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K))
      (fun _ => by simp) (fun _ => Formalism.InvariantFactorPaths.G7.TwoS.integral_X x) h2
    rw [MvPowerSeries.subst_mul hsx, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply hsL hsx] at h4
    exact h4
  have h5 := hsymm _ _ (htrans _ _ _ hΦ (B4.simeq_sum Finset.univ _ _ fun x _ => h3 x))
  obtain ⟨h50, h5I⟩ := h5
  set Bt : MvPowerSeries (Fin N0 × Fin N1) K := ∑ x : Fin N0 × Fin N1, MvPowerSeries.C ((2 : K)⁻¹) *
        subst (fun _ : ZMod 2 => at1 x (lgF K l)) (MvPowerSeries.map j be) with hBt
  have hBt0 : constantCoeff Bt = 0 := by
    rw [map_sub, hΦ0, sub_zero] at h50
    exact h50
  refine ⟨mvExp (Bt - Φ) * U0, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' h5I hU0, ?_⟩
  intro g hg0 hg
  have hsg : HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg0
  have hlg : ∀ y, PowerSeries.subst (g y) (lgF K l) = MvPowerSeries.X y := by
    intro y
    rw [← subst_single_var hsg, at_variable_artin_hasse_eq_one_log]
    exact hg y
  have hgE : (fun x => at1 x (expF K l)) = g := by
    funext y
    have h6 := exp_log exponential_specification hl (hg0 y)
    rw [hlg y] at h6
    exact h6
  rw [hgE]
  have e5 : mvExp (-Φ) = mvExp (Bt - Φ) * mvExp (-Bt) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add h50 (by rw [map_neg, hBt0, neg_zero])]
    congr 1
    ring
  have e6 : subst g (-Bt) = ((-1 : K) / 2) • ∑ x : Fin N0 × Fin N1, subst
      (fun s : ZMod 2 => (if s = 0 then (1 : K) else 1) •
        (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) (MvPowerSeries.map j be) := by
    have hsa : ∀ x : Fin N0 × Fin N1, HasSubst (fun _ : ZMod 2 => at1 x (lgF K l)) := fun x =>
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_inVar_eq_zero x (cc_lgF hl))
    rw [← MvPowerSeries.coe_substAlgHom hsg, map_neg, MvPowerSeries.coe_substAlgHom hsg, hBt,
      subst_sum hsg, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.subst_mul hsg, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply (hsa x) hsg]
    simp only [subst_single_var hsg, hlg, ite_self, one_smul]
    rw [← neg_mul, ← map_neg]
    congr 2
    ring
  unfold thetaOne
  rw [e5, mul_right_comm, MvPowerSeries.subst_mul hsg,
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hsg (by rw [map_neg, hBt0, neg_zero]), e6]

end Formalism.L2.Th1.D
