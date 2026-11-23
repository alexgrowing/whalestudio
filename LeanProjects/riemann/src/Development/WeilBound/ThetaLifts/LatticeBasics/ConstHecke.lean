import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
import GroundTheory.AutomorphicForms.CompactAbelianCharacters

noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (eulerFactor)
open Neutral.B1 (Ideles diagUnits localIdele)
open ReciprocityTheory.Neutral.Bridge

variable {K : Type} [Field K] [NumberField K]

theorem exp_neg_le_norm_inv {z : ℂ} {x : ℝ} (hx : x < 1) (hz : ‖z‖ = x) : Real.exp (-x) ≤ ‖(1 - z)⁻¹‖ := by
  have h0 : 0 < ‖1 - z‖ := lt_of_lt_of_le (by rw [norm_one, hz]; linarith) (norm_sub_norm_le 1 z)
  rw [norm_inv, Real.exp_neg]
  refine inv_anti₀ h0 ((norm_sub_le _ _).trans ?_)
  rw [norm_one, hz, add_comm]
  exact Real.add_one_le_exp x

theorem exp_le_inv {x : ℝ} (hx : x < 1) : Real.exp x ≤ ‖(1 - (x : ℂ))⁻¹‖ := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith),
    le_inv_comm₀ (Real.exp_pos x) (by linarith), ← Real.exp_neg]
  linarith [Real.add_one_le_exp (-x)]

theorem hchar_eq_one (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (χ : HChar K) (hu : χ.IsUnitary)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (h : ∀ w ∉ S, (Ideal.absNorm w.asIdeal).Prime → ∀ x, χ.loc w x = 1) : χ = 1 := by
  classical
  by_contra hne
  obtain ⟨Λ, ⟨hA, hP⟩, -⟩ := (H K χ hu).2 hne
  obtain ⟨C, hC⟩ := exists_bound_primeIdealZetaSum_not_prime (K := K)
  set A : Set (HeightOneSpectrum (𝓞 K)) := {w | ¬ (Ideal.absNorm w.asIdeal).Prime}
  have key : ∀ s : ℝ, 1 < s → Real.exp (NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s -
      2 * (C + hS.toFinset.card)) ≤ ‖Λ s‖ := fun s hs => by
    set x : HeightOneSpectrum (𝓞 K) → ℝ := fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) with hx
    have x0 : ∀ w, 0 ≤ x w := fun w => by positivity
    have x1 : ∀ w, x w < 1 := fun w =>
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith [DedekindZetaReal.two_le_absNorm K w]) (by linarith)
    have xc : ∀ w : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)) = x w := fun w => by
      rw [hx, Complex.ofReal_cpow (Nat.cast_nonneg _)]; simp
    have sx : Summable x := summable_absNorm_rpow K hs
    have s1 : HasSum (fun w => x w - 2 * (A.indicator x w + (hS.toFinset : Set _).indicator x w))
        (∑' w, x w - 2 * (∑' w : A, x w + ∑ w ∈ hS.toFinset, x w)) :=
      sx.hasSum.sub (((hasSum_subtype_iff_indicator.1 (sx.subtype A).hasSum).add
        (hasSum_subtype_iff_indicator.1 (hS.toFinset.hasSum x))).mul_left 2)
    have le : ∀ w, Real.exp (x w - 2 * (A.indicator x w + (hS.toFinset : Set _).indicator x w)) ≤ ‖eulerFactor χ s w‖ := fun w => by
      by_cases hw : w ∈ A ∨ w ∈ (hS.toFinset : Set _)
      · have a1 := Set.indicator_nonneg (s := A) (fun v _ => x0 v) w
        have a2 := Set.indicator_nonneg (s := (hS.toFinset : Set _)) (fun v _ => x0 v) w
        refine le_trans (b := Real.exp (-x w)) (Real.exp_le_exp.2 ?_) ?_
        · rcases hw with hw | hw <;> rw [Set.indicator_of_mem hw] at * <;> linarith
        · unfold eulerFactor
          split_ifs
          · exact exp_neg_le_norm_inv (x1 w) (by
              rw [norm_mul, xc, Complex.norm_real, Real.norm_of_nonneg (x0 w)]
              exact (congrArg (· * x w) (hu _)).trans (one_mul _))
          · rw [norm_one]; exact Real.exp_le_one_iff.2 (by linarith [x0 w])
      · push Not at hw
        have hl := h w (by simpa using hw.2) (not_not.1 hw.1)
        rw [Set.indicator_of_notMem hw.1, Set.indicator_of_notMem hw.2, eulerFactor, if_pos (show χ.UnrAt w from fun y _ => hl y),
          show χ.val w = 1 from hl _, xc]
        simpa using exp_le_inv (x1 w)
    refine le_trans (Real.exp_le_exp.2 ?_) (le_of_tendsto_of_tendsto' s1.rexp (hP s hs).norm fun T =>
      Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun w _ => le w)
    have e1 : ∑' w : A, x w ≤ C := hC s hs
    have e2 : ∑ w ∈ hS.toFinset, x w ≤ hS.toFinset.card := by
      simpa using Finset.sum_le_card_nsmul _ _ 1 fun w _ => (x1 w).le
    rw [NumberField.Set.primeIdealZetaSum_def, tsum_univ x]
    linarith
  have hc : Tendsto (fun s : ℝ => ‖Λ s‖) (𝓝[>] 1) (𝓝 ‖Λ 1‖) :=
    (hA.continuousAt.tendsto.comp ((Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds)).norm
  refine not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.comp
    (tendsto_atTop_add_const_right _ (-(2 * (C + hS.toFinset.card))) (tendsto_primeIdealZetaSum_univ K)))) _ hc
  filter_upwards [self_mem_nhdsWithin] with s hs using key s hs

theorem exists_prime_norm (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∃ w ∉ S, (Ideal.absNorm w.asIdeal).Prime := by
  by_contra hn
  push Not at hn
  obtain ⟨t, ht⟩ := GlobalTheory.HeckeOne.exists_normChar_ne_one (K := K)
  exact ht (hchar_eq_one H _ (GlobalTheory.HeckeOne.isUnitary_normChar t) hS fun w h1 h2 => absurd h2 (hn w h1))

theorem closed_eq_top [IsTotallyComplex K] (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (M : Subgroup (Ideles K))
    (hM : IsClosed (M : Set (Ideles K))) (h1 : ∀ k, diagUnits K k ∈ M) (h2 : GlobalTheory.IdeleCovolume.eIdele K ∈ M)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (h : ∀ w ∉ S, (Ideal.absNorm w.asIdeal).Prime → ∀ x, localIdele K w x ∈ M) (z : Ideles K) : z ∈ M := by
  obtain ⟨C, hC, hc⟩ := GlobalTheory.IdeleCovolume.exists_compact_idele K
  have : CompactSpace (Ideles K ⧸ M) := ⟨by
    refine (hC.image (QuotientGroup.continuous_mk (N := M))).of_isClosed_subset isClosed_univ fun q _ => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, n, hk⟩ := hc y
    exact ⟨_, hk, by
      rw [mul_comm]; exact QuotientGroup.mk_mul_of_mem y (mul_mem (h1 k) (zpow_mem h2 n))⟩⟩
  by_contra hz
  obtain ⟨χ, hχ⟩ := GroundTheory.Automorphic.CompactAbelianFourier.exists_char_ne_one (C := Ideles K ⧸ M) (g := z)
    fun e => hz ((QuotientGroup.eq_one_iff z).1 e)
  let c : Ideles K →* Circle := χ.toMonoidHom.comp (QuotientGroup.mk' M)
  have cc : Continuous c := χ.continuous.comp QuotientGroup.continuous_mk
  have c1 : ∀ y ∈ M, Circle.toUnits (c y) = 1 := fun y hy => by
    rw [show c y = χ (y : Ideles K ⧸ M) from rfl, (QuotientGroup.eq_one_iff y).2 hy, map_one, map_one]
  let X : HChar K := ⟨Circle.toUnits.comp c, Units.continuous_iff.2 ⟨continuous_subtype_val.comp cc,
    (continuous_subtype_val.comp cc.inv).congr fun x => Circle.coe_inv (c x)⟩, fun k => c1 _ (h1 k)⟩
  have := hchar_eq_one H X (fun x => Circle.norm_coe (c x)) hS fun w a b x => c1 _ (h w a b x)
  exact hχ (Circle.ext (congrArg (fun Y : HChar K => ((Y.1 z : ℂˣ) : ℂ)) this))

end GlobalTheory.ThK.Dbl

end
