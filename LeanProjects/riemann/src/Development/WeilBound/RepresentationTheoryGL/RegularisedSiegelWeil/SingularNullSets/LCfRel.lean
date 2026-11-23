import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelC

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set Metric

variable {D : D7} {n : ℕ}

theorem cut_cont {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hE : IsCont H φ s₀ U d E σ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) :
    ContinuousOn (fun p : ℂ × KAt D n v => cutR nb C (E p.1) (g * p.2)) (U ×ˢ univ) := by
  have hterm : ∀ x : hermA D n, ContinuousOn (fun p : ℂ × KAt D n v => E p.1 (g * ↑p.2 * nb x))
      (U ×ˢ univ) := by
    intro x
    have hc : Continuous (fun p : ℂ × KAt D n v => (p.1, g * ↑p.2 * nb x)) :=
      continuous_fst.prodMk ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
        continuous_const)
    exact hE.cont.comp hc.continuousOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  show ContinuousOn (fun p : ℂ × KAt D n v => ∑ x ∈ C.s, C.co x * E p.1 (g * ↑p.2 * nb x)) (U ×ˢ univ)
  exact continuousOn_finsetSum _ (fun x _ => continuousOn_const.mul (hterm x))

theorem cut_bound {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ}
    {σ : ℝ} (hE : IsCont H φ s₀ U d E σ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) {S : Set ℂ}
    (hSU : S ⊆ U) (hS : IsCompact S) : ∃ M, ∀ z ∈ S, ∀ u : KAt D n v, ‖cutR nb C (E z) (g * u)‖ ≤ M := by
  obtain ⟨B, hB⟩ := (hS.prod (isCompact_cset nb C g)).exists_bound_of_continuousOn
    (hE.cont.mono (Set.prod_mono hSU (Set.subset_univ _)))
  refine ⟨∑ x ∈ C.s, ‖C.co x‖ * B, fun z hz u => ?_⟩
  show ‖∑ x ∈ C.s, C.co x * E z (g * ↑u * nb x)‖ ≤ _
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [norm_mul]
  have hmem : (z, g * ↑u * nb x) ∈ S ×ˢ cset nb C g := Set.mk_mem_prod hz (mem_cset nb C g u hx)
  have hb : ‖E z (g * ↑u * nb x)‖ ≤ B := hB _ hmem
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem onU {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hE : IsCont H φ s₀ U d E σ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (hc : Differentiable ℂ c) (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g) (g : G D n) :
    ∀ z ∈ U, ∫ u, cutR nb C (E z) (g * u) ∂νv = c z * E z g := by
  have hh : DifferentiableOn ℂ (fun z => ∫ u, cutR nb C (E z) (g * u) ∂νv) U :=
    diffOn_integral νv (fun z (u : KAt D n v) => cutR nb C (E z) (g * u)) hE.isOpen (cut_cont hE nb C g)
      (fun u => by simp only [cutR]; exact DifferentiableOn.fun_sum fun x _ => (hE.hol _).const_mul _)
      (fun S hSU hS => cut_bound hE nb C g hSU hS)
  have hg : DifferentiableOn ℂ (fun z => c z * E z g) U := hc.differentiableOn.mul (hE.hol g)
  refine eqOn_right hE.isOpen hE.right.1 hE.right.isPreconnected hh hg (max σ ((n : ℝ) / 2)) fun z hz => ?_
  have h1 : σ < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have h2 : (n : ℝ) / 2 < z.re := lt_of_le_of_lt (le_max_right _ _) hz
  have e : ∀ u : KAt D n v, cutR nb C (E z) (g * u) = d.eval z * cutR nb C (eisS (fam H φ s₀ z)) (g * u) := by
    intro u
    simp only [cutR, hE.eq z h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [e]
  rw [integral_const_mul, farRight hH hφc hφl nb C c νv hrel h2 g, hE.eq z h1 g]
  ring

end LCfRel

open LCfRel Set Metric in
theorem cfRel : HtExist → CfRel := by
  intro _ D n χ _ H hH s₀ φ hφc hφl U d E σ hE ε hrad nb _ v C c hc νv hν hrel k hk hvan g
  haveI : IsProbabilityMeasure νv := hν
  obtain ⟨hε, hball, hne⟩ := hrad
  have hsph : Metric.sphere s₀ ε ⊆ U := fun z hz => hball (Metric.sphere_subset_closedBall hz)
  have hdne : ∀ z ∈ Metric.sphere s₀ ε, Polynomial.eval z d ≠ 0 := by
    intro z hz
    refine hne z (Metric.sphere_subset_closedBall hz) ?_
    rintro rfl
    rw [Metric.mem_sphere, dist_self] at hz
    linarith
  have hEc : ∀ y, ContinuousOn (fun z => E z y) (Metric.sphere s₀ ε) :=
    fun y => ((hE.hol y).continuousOn).mono hsph
  have hdc : ContinuousOn (fun z => Polynomial.eval z d) (Metric.sphere s₀ ε) :=
    (Polynomial.continuous d).continuousOn
  have hpc : ContinuousOn (fun z : ℂ => (z - s₀) ^ (k - 1)) (Metric.sphere s₀ ε) :=
    ((continuous_id.sub continuous_const).pow _).continuousOn
  have hstep1 : ∀ u : KAt D n v, cutR nb C (cf d E s₀ ε k) (g * ↑u) =
      (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε),
        (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d) := by
    intro u
    have hcs := circle_sum C.s C.co
      (fun x z => (z - s₀) ^ (k - 1) * (E z (g * ↑u * nb x) / Polynomial.eval z d)) s₀ hε.le
      (fun x _ => hpc.mul ((hEc _).div hdc hdne))
    beta_reduce at hcs
    have hsum : (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d)) =
        ∑ x ∈ C.s, C.co x * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (E z (g * ↑u * nb x) / Polynomial.eval z d) := by
      rw [← hcs]
      refine circleIntegral.integral_congr hε.le (fun z _ => ?_)
      show (z - s₀) ^ (k - 1) * ((∑ x ∈ C.s, C.co x * E z (g * ↑u * nb x)) / Polynomial.eval z d) = _
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum, Finset.mul_sum]
    show ∑ x ∈ C.s, C.co x * cf d E s₀ ε k (g * ↑u * nb x) = _
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show C.co x * ((2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε),
      (z - s₀) ^ (k - 1) * (E z (g * ↑u * nb x) / Polynomial.eval z d)) = _
    ring
  have hcont2 : ContinuousOn (fun p : ℂ × KAt D n v =>
      (p.1 - s₀) ^ (k - 1) * (cutR nb C (E p.1) (g * ↑p.2) / Polynomial.eval p.1 d))
      (Metric.sphere s₀ ε ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℂ × KAt D n v => cutR nb C (E p.1) (g * ↑p.2))
        (Metric.sphere s₀ ε ×ˢ univ) :=
      (cut_cont hE nb C g).mono (Set.prod_mono hsph subset_rfl)
    exact (hpc.comp continuousOn_fst (fun p hp => hp.1)).mul
      (h1.div (hdc.comp continuousOn_fst (fun p hp => hp.1)) (fun p hp => hdne p.1 hp.1))
  have hbound : ∃ M, ∀ z ∈ Metric.sphere s₀ ε, ∀ u : KAt D n v,
      ‖(z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d)‖ ≤ M := by
    obtain ⟨M1, hM1⟩ := cut_bound hE nb C g hsph (isCompact_sphere s₀ ε)
    obtain ⟨A, hA⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn hpc
    obtain ⟨B, hB⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn (hdc.inv₀ hdne)
    refine ⟨A * (M1 * B), fun z hz u => ?_⟩
    rw [norm_mul, div_eq_mul_inv, norm_mul]
    have hA' : ‖(z - s₀) ^ (k - 1)‖ ≤ A := hA z hz
    have hM' : ‖cutR nb C (E z) (g * ↑u)‖ ≤ M1 := hM1 z hz u
    have hB' : ‖(Polynomial.eval z d)⁻¹‖ ≤ B := hB z hz
    exact mul_le_mul hA' (mul_le_mul hM' hB' (norm_nonneg _) ((norm_nonneg _).trans hM'))
      (by positivity) ((norm_nonneg _).trans hA')
  obtain ⟨M, hM⟩ := hbound
  have hswap := circle_swap νv
    (fun z (u : KAt D n v) => (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d))
    s₀ hε.le hcont2 hM
  beta_reduce at hswap
  have hinner : ∀ z ∈ Metric.sphere s₀ ε,
      ∫ u, (z - s₀) ^ (k - 1) * (cutR nb C (E z) (g * ↑u) / Polynomial.eval z d) ∂νv =
        (z - s₀) ^ (k - 1) * (c z * (E z g / Polynomial.eval z d)) := by
    intro z hz
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
      onU hH hφc hφl hE nb C c hc νv hrel g z (hsph hz)]
    ring
  have hvan' : ∀ j : ℕ, k < j →
      ∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * (E z g / Polynomial.eval z d) = 0 := by
    intro j hj
    have h0' : (2 * ↑Real.pi * Complex.I)⁻¹ *
        ∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * (E z g / Polynomial.eval z d) = 0 :=
      congrFun (hvan j hj) g
    rcases mul_eq_zero.1 h0' with h | h
    · exact absurd h (inv_ne_zero Complex.two_pi_I_ne_zero)
    · exact h
  have hce := circle_entire_mul c hc (fun z => E z g / Polynomial.eval z d) s₀ hε
    ((hEc g).div hdc hdne) k hk hvan'
  beta_reduce at hce
  show ∫ u, cutR nb C (cf d E s₀ ε k) (g * ↑u) ∂νv = c s₀ * cf d E s₀ ε k g
  simp_rw [hstep1]
  rw [MeasureTheory.integral_const_mul, ← hswap, circleIntegral.integral_congr hε.le hinner, hce]
  show _ = c s₀ * ((2 * ↑Real.pi * Complex.I)⁻¹ *
    ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (E z g / Polynomial.eval z d))
  ring

end PositivityTheory.Rg.Rsw.L

end
