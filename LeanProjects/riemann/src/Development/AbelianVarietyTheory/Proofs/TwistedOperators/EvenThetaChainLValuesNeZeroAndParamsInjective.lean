import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegersStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ChainVal

variable {D : D7}

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_same (χ : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    GlobalTheory.ChainOnto.stepPar χ χ t B = B + GlobalTheory.LFun.segFam (vf χ) t := by
  funext w; simp [GlobalTheory.ChainOnto.stepPar, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = B + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i)) c.t := by
  induction k with
  | zero => simp [chainPar]
  | succ k ih => rw [chainPar_succ, ih, stepPar_same, Finset.sum_range_succ, add_assoc]

theorem chainPar_twist (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹ =
      GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i * (c.χ k)⁻¹)) c.t := by
  rw [chainPar_closed, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam]
  congr 1
  funext w; simp [vf, mul_comm]

theorem locL_finsetSum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (d : ι → GlobalTheory.LFun.Fam K)
    (w : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    GlobalTheory.LFun.locL (∑ i ∈ s, d i) w x = ∏ i ∈ s, GlobalTheory.LFun.locL (d i) w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [GlobalTheory.LFun.locL]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, GlobalTheory.LFun.locL_add, ih]

theorem bounded_single {K : Type} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) : GlobalTheory.LFun.Bounded T (fun w => {z w}) 1 0 :=
  fun w _ => ⟨by simp, fun b hb => by rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, hz]⟩

theorem eulerProd_add_segFam {K : Type} [Field K] [NumberField K] {ι : Type} (T : Set (HeightOneSpectrum (𝓞 K)))
    (A : GlobalTheory.LFun.Fam K) (s : Finset ι) (z : ι → HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (x : ℂ)
    (hA : GlobalTheory.LFun.Converges T A x)
    (hz : ∀ i ∈ s, ∀ l < t, GlobalTheory.LFun.Converges T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :
    GlobalTheory.LFun.eulerProd T (A + ∑ i ∈ s, GlobalTheory.LFun.segFam (z i) t) x = GlobalTheory.LFun.eulerProd T A x *
      ∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l) := by
  have h1 : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ s, ∏ l ∈ Finset.range t,
      GlobalTheory.LFun.locL (fun u => {z i u}) w (x + ((t : ℂ) - 1) / 2 - l))
      (∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :=
    hasProd_prod fun i hi => hasProd_prod fun l hl => (hz i hi l (Finset.mem_range.1 hl)).hasProd
  have h2 := hA.hasProd.mul h1
  show ∏' w : {w // w ∉ T}, _ = _
  refine HasProd.tprod_eq ?_
  convert h2 using 1
  funext w
  rw [GlobalTheory.LFun.locL_add, locL_finsetSum]
  simp only [GlobalTheory.LFun.locL_segFam']

end GlobalTheory.EvenOnto.ChainVal

open GlobalTheory.EvenOnto.ChainVal in

theorem GlobalTheory.EvenOnto.chainL_and_inj : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  intro D
  refine ⟨?_, ?_⟩
  · intro c hc B hB k hk
    set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
    have hnt : c.n + 2 ≤ c.t := hc.step
    have hnt' : (c.n : ℝ) + 2 ≤ c.t := by exact_mod_cast hnt
    have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.range k → Differentiable ℂ Λ ∧
        (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
          (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ k)⁻¹) w}) z) ∧
        ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
      intro i
      by_cases hi : i ∈ Finset.range k
      · obtain ⟨Λ, h⟩ := GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers D c hc i k (Finset.mem_range.1 hi) hk
        exact ⟨Λ, fun _ => h⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose Λ hΛ using hΛ
    set A := GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ with hA
    have hAb : GlobalTheory.LFun.Bounded T A c.n (((c.n : ℝ) - 1) / 2) :=
      hB.twist fun w _ => by simp [vf, GlobalTheory.LFun.norm_val]
    let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => vf (c.χ i * (c.χ k)⁻¹)
    have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
      (bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
    let H : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
      ∏ i ∈ Finset.range k, ∏ l ∈ Finset.range c.t, Λ i (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l)
    have hEq : ∀ x : ℂ, ((c.n : ℝ) + c.t + 2) < x.re →
        H x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.χ k) (x + 1 / 2) := by
      intro x hx
      have hre : ∀ l : ℕ, l < c.t → 1 < (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l).re := by
        intro l hl
        have : (l : ℝ) + 1 ≤ c.t := by exact_mod_cast hl
        have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _
        simp
        linarith
      show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
        (GlobalTheory.LFun.val (F := D.host.F) (c.χ k))⁻¹) (x + 1 / 2)
      change _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹) (x + 1 / 2)
      rw [chainPar_twist, ← hA, eulerProd_add_segFam T A (Finset.range k) z c.t (x + 1 / 2)
        (hAb.converges (by have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _; simp; linarith))
        (fun i _ l hl => hzc i _ (hre l hl))]
      refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi =>
        Finset.prod_congr rfl fun l hl => ?_)
      exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
    have hU : IsOpen (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
    have hD : DifferentiableOn ℂ H (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := by
      refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
      · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
        simp only [GlobalTheory.Cont.mem_rightOf] at hx
        simp
        linarith
      · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
          (hΛ i hi).1.comp (by fun_prop)
    have hAn := hD.analyticOnNhd hU
    have hmem : ((c.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2) := by
      simp only [GlobalTheory.Cont.mem_rightOf]
      simp
      linarith
    refine ⟨H ((c.t : ℂ) / 2), ?_, H, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (c.n : ℝ) + c.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, rfl⟩
    refine mul_ne_zero ((hAb.converges ?_).ne_zero) ?_
    · simp
      linarith
    · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun l hl => ?_
      have hl' := Finset.mem_range.1 hl
      have e : (c.t : ℂ) / 2 + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l = ((c.t - l : ℕ) : ℂ) := by
        rw [Nat.cast_sub hl'.le]
        ring
      rw [e]
      exact (hΛ i hi).2.2 _ (by omega)
  · intro c k B B' w h
    induction k with
    | zero => simpa [chainPar] using h
    | succ k ih =>
      apply ih
      rw [chainPar_succ, chainPar_succ] at h
      simp only [GlobalTheory.ChainOnto.stepPar] at h
      have h2 := add_right_cancel h
      exact Multiset.map_injective (mul_right_injective _) h2

end
