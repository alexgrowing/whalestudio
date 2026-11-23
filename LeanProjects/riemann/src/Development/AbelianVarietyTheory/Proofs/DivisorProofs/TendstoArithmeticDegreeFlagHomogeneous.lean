import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeAndArithmeticCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGreenPotentialWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBoundaryPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralConstantFlagDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoMixedIntegralBoundaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlatLimit
open Filter Topology MvPolynomial

theorem limVal : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O A _ _ _ =>
    ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) (Q : GlobalTheory.FlagPoly.Pol D.what₂.Tau O.Y.N),
      Q.IsHomogeneous (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) →
      Filter.Tendsto (fun R => O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R (GlobalTheory.FlagPoly.pSum τ 1 * Q) -
        ∑ c, O.Y.htDetT B c τ * (A.w c * Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N Q)) Filter.atTop (nhds 0) := by
  intro hX hP hH hSW D O hC hf A T H h B hB τ Q hQ
  have hTie := (GlobalTheory.T.degree_and_arithmetic_compatibility hP hH D O hC hf A T H h).1
  set e : Wt O.Y := fun σ' _ => if σ' = τ then (-1 : ℝ) else 0 with he
  have hlin : Formalism.DegreeFormula.linRoot e = GlobalTheory.FlagPoly.pSum τ 1 := by
    simp only [Formalism.DegreeFormula.linRoot, GlobalTheory.FlagPoly.pSum, he, pow_one]
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib, Finset.sum_eq_single τ]
    · simp
    · intro b _ hb; simp [hb]
    · simp

  let P : GlobalTheory.FlagPoly.Pol D.what₂.Tau O.Y.N → Prop := fun Q => Tendsto (fun R =>
    O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R (GlobalTheory.FlagPoly.pSum τ 1 * Q) -
      ∑ c, O.Y.htDetT B c τ * (A.w c * Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N Q)) atTop (𝓝 0)
  have key : ∀ u : Wt O.Y, (∀ σ, StrictAnti (u σ)) → P (Formalism.DegreeFormula.linRoot u ^ Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) := by
    intro u hu
    have hdom : DomL O.Y.j u := fun σ a b hab _ => ((hu σ) (by rw [Fin.lt_def]; omega)).le
    have hsm := GlobalTheory.T.smooth_green_potential_weight hP hH D O hC hf A T H h
    have hF1 := GlobalTheory.T.exists_smooth_boundary_potential hX hP hH hSW D O hC hf A T H h B hB τ
    have hdeg := GlobalTheory.T.mixed_integral_constant_flag_degree hP hH D O hC hf A T H h B hB
    choose g hg hgph hgv using hF1
    have hint := fun c => GlobalTheory.T.tendsto_mixed_integral_boundary hP hH D O hC hf A T H h B hB τ c u hdom (g c) (hg c) (hgph c)
    have hsum := tendsto_finsetSum Finset.univ fun c _ => hint c
    rw [Finset.sum_const_zero] at hsum
    refine hsum.congr' ?_
    · filter_upwards [eventually_ge_atTop (Real.exp 2)] with R hR
      rw [← hlin, GlobalTheory.T.arithmetic_degree_mixed_linear_root D O.Y T hTie B hB R hR e u, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      have e1 : T.L B c e + (T.K B c).ar ((T.F c).phR R e) =
          (T.L B c e + (T.K B c).ar (g c)) + (T.K B c).ar ((T.F c).phR R e) + (-1 : ℝ) • (T.K B c).ar (g c) := by
        rw [neg_one_smul]; abel
      rw [e1, MultilinearMap.cons_add, MultilinearMap.cons_add, MultilinearMap.cons_smul, hgv c u _ (hsm c R hR u),
        (T.K B c).num_ar _ (hsm c R hR e), (T.K B c).num_ar _ (hg c), hdeg c u _ (hsm c R hR u)]
      show _ = _ - _
      simp only [Formalism.DegreeFormula.flagDeg]
      ring
  have hspan := GlobalTheory.T.homogeneous_mem_span_linear_roots D.what₂.Tau O.Y.N (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) Q hQ
  show P Q
  clear hQ
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact key u hu
  | zero =>
    show Tendsto _ _ _
    simp only [mul_zero, map_zero]
    have : Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N 0 = 0 := by simp [Formalism.DegreeFormula.degFl]
    simp only [this, mul_zero, Finset.sum_const_zero, sub_zero]
    exact tendsto_const_nhds
  | add x y _ _ hx hy =>
    show Tendsto _ _ _
    have hd : Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N (x + y) =
        Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N x + Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N y := by
      simp only [Formalism.DegreeFormula.degFl, coeff_add, mul_add, Finset.sum_add_distrib]
    have hxy := hx.add hy
    rw [add_zero] at hxy
    refine hxy.congr fun R => ?_
    simp only [mul_add, map_add, hd, Finset.sum_add_distrib]
    ring
  | smul a x _ hx =>
    show Tendsto _ _ _
    have hd : Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N (a • x) = a * Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N x := by
      simp only [Formalism.DegreeFormula.degFl, coeff_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have := hx.const_mul a
    rw [mul_zero] at this
    refine this.congr fun R => ?_
    simp only [mul_smul_comm, map_smul, smul_eq_mul, hd, mul_sub, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun c _ => by ring)

end GlobalTheory.FlatLimit
