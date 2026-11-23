import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.ThetaShiftInversion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummandStatement

noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latOf_discrete [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) :
    DiscreteTopology (latOf N) := GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage F N

theorem latOf_isZLattice [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] : IsZLattice ℝ (latOf N) := GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage F N hN

theorem covolume_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)] :
    ZLattice.covolume (latOf N) = covol N := GlobalTheory.T.covolume_fractionalIdealRealLatticeImage F N hN

theorem dual_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual F N hN

theorem fourier_lipschitzOneVariableKernel (k : ℕ) (hk : 2 ≤ k) (he : Even k) (w : ℂ) (hw : w.im ≠ 0) (x : ℝ) :
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) :=
  GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq k hk he w hw x

theorem Phi_cont_decay (k : ℕ) (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧
      ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel F k hk z hz

theorem summable_lhsTerm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) (hM : M ≠ 0) (k : ℕ)
    (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Summable (fun a : (M : Set F) => lhsTerm k z a) := GlobalTheory.T.summable_lipschitzLatticeNormPowSummand F M hM k hk z hz

theorem fourier_prod_coord (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_injective [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem Phi_remb (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) :
    Phi k z (remb F ν) =
      if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 := by
  unfold Phi
  by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
  · rw [if_pos hc, Finset.prod_congr rfl fun τ _ => by rw [remb_apply, phi1, if_pos (hc τ)],
      Finset.prod_mul_distrib, ← Complex.exp_sum, rhsTerm, Finset.abs_prod, ← Finset.prod_pow, Complex.ofReal_prod]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨τ, hτ⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [remb_apply, phi1, if_neg (not_lt.2 hτ)])

theorem fourier_Phi (k : ℕ) (hk : 2 ≤ k) (he : Even k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0)
    (a : F) : 𝓕 (Phi k z) (remb F a) =
      (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ) *
        lhsTerm k z (-a) := by
  rw [show Phi k z = fun ξ : RSp F => ∏ τ, phi1 k (z τ) (ξ τ) from rfl, fourier_prod_coord]
  simp only [remb_apply]
  have h := fun τ : F →+* ℝ => fourier_lipschitzOneVariableKernel k hk he (z τ) (hz τ) (τ a)
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, lhsTerm, Finset.prod_zpow]
  simp [map_neg, sub_eq_add_neg]

theorem lipschitz : Lipschitz := by
  intro F _ _ _ M hM k hk he z hz
  haveI : DiscreteTopology (latOf M) := latOf_discrete M
  haveI : IsZLattice ℝ (latOf M) := latOf_isZLattice M hM
  set L := Formalism.H.dual (latOf M) with hL
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) (latOf M)
  haveI : DiscreteTopology L := h1
  haveI : IsZLattice ℝ L := h2
  have hdd : Formalism.H.dual L = latOf M := Formalism.H.dualDual (RSp F) (latOf M)
  have hcov : ZLattice.covolume L = (covol M)⁻¹ := by
    rw [Formalism.H.covolumeDual (RSp F) (latOf M), covolume_latOf M hM]
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ FractionalIdeal.dual ℤ ℚ M, remb F ν = x := by
    intro x; rw [hL, dual_latOf M hM]; exact mem_latOf _ x
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ M, remb F a = x := by
    intro x; rw [hdd]; exact mem_latOf _ x
  obtain ⟨hcont, hdec⟩ := Phi_cont_decay k hk z hz
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L (Phi k z) hcont
    ((Module.finrank ℝ (RSp F) : ℝ) + 1) (by linarith) (hdec _)
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 (Phi k z) μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L (Phi k z) hint D hD μ μ.2

  let eM : (M : Set F) ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hDmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  let eD : (FractionalIdeal.dual ℤ ℚ M : Set F) ≃ L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hLmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  set cst : ℂ := (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ)
  have hsL := summable_lhsTerm M hM k hk z hz
  let eN : (M : Set F) ≃ (M : Set F) :=
    ⟨fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => by simp, fun a => by simp⟩
  have hsLn : Summable (fun a : (M : Set F) => lhsTerm k z (-(a : F))) :=
    (eN.summable_iff (f := fun a : (M : Set F) => lhsTerm k z a)).2 hsL
  have hFM : ∀ a : (M : Set F), 𝓕 (Phi k z) (eM a) = cst * lhsTerm k z (-(a : F)) :=
    fun a => fourier_Phi k hk he z hz a
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact (hsLn.mul_left cst).congr fun a => (hFM a).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Phi k z ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have H4' : HasSum (fun a : (M : Set F) => (covol M : ℂ) * cst * lhsTerm k z (-(a : F)))
      (∑' l : L, Phi k z (l : RSp F)) := by
    refine H4.congr_fun fun a => ?_
    simp only [Function.comp_apply, hFM, hcov, Complex.ofReal_inv, inv_inv]
    ring
  have hs0 : Summable (fun l : L => Phi k z (l : RSp F)) := by
    simpa using hsumx 0
  set g : F → ℂ := fun ν =>
    if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 with hg
  have hind : (FractionalIdeal.dual ℤ ℚ M : Set F).indicator g = (dualCone M z).indicator (rhsTerm k z) := by
    funext ν
    by_cases hν : ν ∈ (FractionalIdeal.dual ℤ ℚ M : Set F)
    · have hν' : ν ∈ traceDual M := (mem_traceDual_iff hM ν).2 hν
      by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
      · rw [Set.indicator_of_mem hν, Set.indicator_of_mem (show ν ∈ dualCone M z from ⟨hν', hc⟩), hg]
        simp [hc]
      · rw [Set.indicator_of_mem hν, Set.indicator_of_notMem (show ν ∉ dualCone M z from fun h => hc h.2), hg]
        simp [hc]
    · have hν' : ν ∉ dualCone M z := fun h => hν ((mem_traceDual_iff hM ν).1 h.1)
      rw [Set.indicator_of_notMem hν, Set.indicator_of_notMem hν']
  have hPg : ∀ ν : (FractionalIdeal.dual ℤ ℚ M : Set F), Phi k z (eD ν) = g ν := fun ν => Phi_remb k z ν
  have hsD : Summable (fun ν : (FractionalIdeal.dual ℤ ℚ M : Set F) => g ν) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hPg ν
  have hsR : Summable (fun ν : dualCone M z => rhsTerm k z ν) := by
    have h3 := (summable_subtype_iff_indicator (s := (FractionalIdeal.dual ℤ ℚ M : Set F)) (f := g)).1 hsD
    rw [hind] at h3
    exact (summable_subtype_iff_indicator (s := dualCone M z) (f := rhsTerm k z)).2 h3
  have hR : ∑' l : L, Phi k z (l : RSp F) = ∑' ν : dualCone M z, rhsTerm k z ν := by
    rw [← eD.tsum_eq, tsum_subtype (dualCone M z) (rhsTerm k z), ← hind, ← tsum_subtype]
    exact tsum_congr fun ν => hPg ν
  have hLn : ∑' a : (M : Set F), lhsTerm k z (-(a : F)) = ∑' a : (M : Set F), lhsTerm k z a :=
    eN.tsum_eq (fun a : (M : Set F) => lhsTerm k z a)
  have hmain := H4'.tsum_eq
  rw [tsum_mul_left, hLn, hR] at hmain
  refine ⟨hsL, hsR, ?_⟩
  rw [← hmain]
  have hc0 : (covol M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (covol_pos hM).ne'
  have hf0 : ((k - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [lipConst, cst, card_realEmb, div_pow, pow_mul]
  field_simp

end GlobalTheory.LipschitzTR
