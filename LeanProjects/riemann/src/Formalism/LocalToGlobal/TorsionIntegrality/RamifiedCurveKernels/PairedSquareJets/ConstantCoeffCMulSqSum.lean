import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace PairedSquareConstantCoefficients

section Alg

variable {K : Type} [Field K]

theorem isPt_X (R : Subring K) {σ : Type} (a : σ) : IsPt R (MvPowerSeries.X a : MvPowerSeries σ K) := by
  classical
  refine ⟨by simp, fun n => ?_⟩
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem biadd_formal_mul_zero {l linv ph : PowerSeries K} (h : IsLogPair l linv)
    (hph : PowerSeries.constantCoeff ph = 0) {σ : Type} (x : MvPowerSeries σ K) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : be0 l linv ph (fmul l linv 0 x) y = 0 := by
  rw [Pts.fmul_zero_left h, be0, Pts.zero_fadd h hy, PowerSeries.subst_zero_of_constantCoeff_zero hph,
    sub_zero, sub_self]

theorem flin_reindex {σ : Type} (l linv : PowerSeries K) {ν ν' : Type} [Fintype ν] [Fintype ν']
    (e : ν' ≃ ν) (c : ν → K) (u : ν → MvPowerSeries σ K) :
    flin l linv (fun j => c (e j)) (fun j => u (e j)) = flin l linv c u := by
  unfold flin
  rw [Equiv.sum_comp e (fun a => MvPowerSeries.C (c a) * PowerSeries.subst (u a) l)]

theorem constantCoeff_phSum {n : Type} [Fintype n] (c : n → K) {ph : PowerSeries K}
    (hph : PowerSeries.constantCoeff ph = 0) : MvPowerSeries.constantCoeff (phSum c ph) = 0 := by
  unfold phSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul,
    Pts.constantCoeff_subst (MvPowerSeries.constantCoeff_X i) hph, mul_zero]

theorem constantCoeff_sqSum {n : Type} [Fintype n] (c : n → K) :
    MvPowerSeries.constantCoeff (sqSum c) = 0 := by
  simp [sqSum]

theorem constantCoeff_C_mul_sqSum {n : Type} [Fintype n] (s : K) (c : n → K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.C s * sqSum c) = 0 := by
  rw [map_mul, constantCoeff_sqSum, mul_zero]

theorem inBlock_mul {ι B : Type} (k : B) (f g : MvPowerSeries ι K) :
    inBlock k (f * g) = inBlock k f * inBlock k g := by
  simp only [HurwitzJetIntegrality.inBlock_eq_rename, map_mul]

theorem tensor_four_mul {ι : Type} (f g : MvPowerSeries ι K) : tens4 (f * g) = tens4 f * tens4 g := by
  unfold tens4
  simp only [inBlock_mul, Finset.prod_mul_distrib]

theorem constantCoeff_inBlock {ι B : Type} (k : B) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (inBlock k f) = 0 := by
  have h := HurwitzJetIntegrality.coeff_inBlock_embDomain k f 0
  rw [Finsupp.embDomain_zero] at h
  simpa [hf] using h

theorem sum_inBlock_sqSum {ι B : Type} [Fintype ι] [Fintype B] (s : K) (c : ι → K) :
    ∑ k : B, inBlock k (MvPowerSeries.C s * sqSum c) =
      MvPowerSeries.C s * sqSum (fun a : B × ι => c a.2) := by
  simp [HurwitzJetIntegrality.inBlock_eq_rename, sqSum, Finset.mul_sum, Fintype.sum_prod_type]
  rfl

variable [CharZero K]

theorem inBlock_mvExp {ι B : Type} [Finite ι] (k : B) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : inBlock k (mvExp f) = mvExp (inBlock k f) := by
  unfold inBlock
  exact mvSubst_mvExp hf
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _)

theorem tensor_four_exp_quadratic {ι : Type} [Fintype ι] (s : K) (c : ι → K) :
    tens4 (mvExp (MvPowerSeries.C s * sqSum c)) =
      mvExp (MvPowerSeries.C s * sqSum (fun a : Fin 4 × ι => c a.2)) := by
  unfold tens4
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.C s * sqSum c) = 0 :=
    constantCoeff_C_mul_sqSum s c
  rw [Finset.prod_congr rfl (fun k _ => inBlock_mvExp k h0),
    ← mvExp_sum Finset.univ (fun k : Fin 4 => inBlock k (MvPowerSeries.C s * sqSum c))
      (fun k _ => constantCoeff_inBlock k h0),
    sum_inBlock_sqSum]

theorem phIso_cong (R : Subring K) {l linv ph : PowerSeries K} (hF : Frame R l linv ph)
    (h1 : F1 R l linv ph) {O : Type} [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {m ν : Type} [Fintype m] [Fintype ν] [DecidableEq ν] (g : ν → O) (δ : m → ν → O)
    (hδ : ∀ a b, ∑ i, star (δ i a) * δ i b = if a = b then g a else 0) :
    Cong R (phIso τ l linv ph δ) (phSum (fun a => τ (g a)) ph) := by
  have e : ν ≃ Fin (Fintype.card ν) := Fintype.equivFin ν
  have key := gramFormula K R l linv ph hF O τ hE hB h1 hN hA m (Fintype.card ν)
    (fun i j => δ i (e.symm j)) ν (fun j => MvPowerSeries.X (e.symm j)) (fun j => isPt_X R _)
  have e1 : (∑ i, PowerSeries.subst (flin l linv (fun j => τ (δ i (e.symm j)))
      (fun j => (MvPowerSeries.X (e.symm j) : MvPowerSeries ν K))) ph) = phIso τ l linv ph δ := by
    unfold phIso
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [flin_reindex l linv e.symm (fun a => τ (δ i a)) (fun a => MvPowerSeries.X a)]
  have e2 : (∑ j, τ (∑ i, star (δ i (e.symm j)) * δ i (e.symm j)) •
      PowerSeries.subst (MvPowerSeries.X (e.symm j) : MvPowerSeries ν K) ph) =
      phSum (fun a => τ (g a)) ph := by
    unfold phSum
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hδ, if_pos rfl]
  have e3 : (∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
      be0 l linv ph (fmul l linv (τ (∑ i, star (δ i (e.symm j')) * δ i (e.symm j)))
        (MvPowerSeries.X (e.symm j) : MvPowerSeries ν K)) (MvPowerSeries.X (e.symm j'))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' hj' => ?_
    have hne : e.symm j' ≠ e.symm j := fun hh =>
      (ne_of_gt (Finset.mem_filter.1 hj').2) (e.symm.injective hh)
    rw [hδ, if_neg hne, map_zero]
    exact biadd_formal_mul_zero hF.1 hF.2.2 _ (MvPowerSeries.constantCoeff_X _)
  rw [e1, e2, e3, add_zero] at key
  exact key

end Alg

end PairedSquareConstantCoefficients

open PairedSquareConstantCoefficients

theorem IntAtD_of (hO : ShapeOrth) : IntAtD := by
  intro K _ _ _ l linv ph d hF hl h1 hS O _ _ τ hE hB hN hA n m _ _ _ w hw δ hδ Th G hG hTh
  set R := unitBall K with hR
  set c : Fin 4 × n → K := fun a => τ (w a.2) with hc
  set s : K := jet l ph 2 / 2 with hs

  have hcong : Cong R (phIso τ l linv ph δ) (phSum c ph) :=
    phIso_cong R hF h1 τ hE hB hN hA (fun a : Fin 4 × n => w a.2) δ hδ
  have hneg : LG R (-(phIso τ l linv ph δ - phSum c ph)) := (lGSubgroup K R _).2.2 _ hcong
  have hP0 : MvPowerSeries.constantCoeff (-(phSum c ph)) = 0 := by
    rw [map_neg, constantCoeff_phSum c hF.2.2, neg_zero]
  have hexp : mvExp (-(phIso τ l linv ph δ)) =
      mvExp (-(phSum c ph)) * mvExp (-(phIso τ l linv ph δ - phSum c ph)) := by
    rw [← mvExp_add hP0 hneg.1]
    congr 1
    ring
  have hG' : IntMv R (mvExp (-(phIso τ l linv ph δ - phSum c ph)) * G) := IntegralMvPolynomialLemmas.intMv_mul hneg.2 hG
  have hcn : ∀ a, ‖c a‖ ≤ 1 := by
    intro a
    have := hB (w a.2) (hw a.2) 1
    have h2 : binom (τ (w a.2)) 1 = τ (w a.2) := by simp [binom]
    rw [h2] at this
    exact this
  obtain ⟨J4, hJ4, hJ4e⟩ := hO K l linv ph d hF.1 hl hF.2.2 hS (Fin 4 × n) c hcn _ hG'
  rw [← mul_assoc, ← hexp, ← hTh] at hJ4e

  have hq0 := constantCoeff_C_mul_sqSum s (fun j => τ (w j))
  have hq40 := constantCoeff_C_mul_sqSum s c
  refine ⟨mvExp (MvPowerSeries.C s * sqSum (fun j => τ (w j))) * Th, ?_, ?_⟩
  · rw [jets_in_norm_holds K n]
    refine jets_fourth_holds K R n _ ?_ ?_
    · intro x hx
      have hx' : ‖x‖ ^ 4 ≤ 1 := by rw [← norm_pow]; exact hx
      exact pow_le_one_iff_of_nonneg (norm_nonneg x) (by norm_num) |>.1 hx'
    · rw [tensor_four_mul, tensor_four_exp_quadratic, hJ4e, ← mul_assoc, mvExp_mul_neg hq40, one_mul]
      exact (jets_in_norm_holds K _ J4).1 hJ4
  · rw [← mul_assoc, mvExp_neg hq0, one_mul]

end Formalism.L2.Th1.G
