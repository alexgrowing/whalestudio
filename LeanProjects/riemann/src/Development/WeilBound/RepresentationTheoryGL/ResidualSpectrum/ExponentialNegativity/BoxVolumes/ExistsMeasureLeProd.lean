import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.MeasureBoxRingEquivLe
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.SumRangeSuccMulSubPred

open NumberField MeasureTheory Set Matrix
open scoped NNReal ENNReal Pointwise
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace PositivityTheory.Rg.Rs.boxvol

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_measure_le_prod (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (E : Set (AdelicGLn.AdelicGL K n))
      (S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion)) (F : Set (AdelicGLn.FiniteAdelicGL K n)),
      (∀ g ∈ E, (∀ w, infAt w g ∈ S w) ∧ (AdelicGLn.prodEquiv K n g).2 ∈ F) →
      μ E ≤ c * ((∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
        (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F) := by
  set e := infFinEquiv (K := K) (n := n) with he
  set ρ : Measure ((Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n) :=
    (Measure.pi fun w => (Measure.haar : Measure (GL (Fin n) w.Completion))).prod
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) with hρ
  have hν : (Measure.map e μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ e.toMulEquiv e.continuous e.symm.continuous
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map e μ) ρ
  set s := (Measure.map e μ).haarScalarFactor ρ with hs
  refine ⟨(s : ℝ≥0∞), ENNReal.coe_ne_top, fun E S F hE => ?_⟩
  have hρT : ρ ((Set.univ.pi S) ×ˢ F) = (∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F := by
    rw [hρ, Measure.prod_prod, Measure.pi_pi]
  have hET : E ⊆ e ⁻¹' ((Set.univ.pi S) ×ˢ F) := fun g hg => ⟨fun w _ => (hE g hg).1 w, (hE g hg).2⟩
  calc μ E ≤ μ (e ⁻¹' ((Set.univ.pi S) ×ˢ F)) := measure_mono hET
    _ = Measure.map e μ ((Set.univ.pi S) ×ˢ F) := (e.toHomeomorph.toMeasurableEquiv.map_apply _).symm
    _ = (s • ρ) ((Set.univ.pi S) ×ˢ F) := by rw [← heq]
    _ = _ := by rw [Measure.smul_apply, hρT, ENNReal.smul_def, smul_eq_mul]

end PositivityTheory.Rg.Rs.boxvol

namespace PositivityTheory.Rg.Rs

open boxvol in
theorem boxvol_holds : An.BoxVol := by
  intro K _ _ n μ _ ω hω hωB
  rcases n with _ | m
  · have hs : (Set.univ : Set (AdelicGLn.AdelicGL K 0)).Subsingleton := fun x _ y _ =>
      Units.ext (Subsingleton.elim _ _)
    have hfin : μ univ ≠ ⊤ := hs.isCompact.measure_lt_top.ne
    refine ⟨(μ univ).toReal, fun x => ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty, neg_zero, Real.exp_zero, mul_one]
    rw [ENNReal.ofReal_toReal hfin]
    exact measure_mono (subset_univ _)
  obtain ⟨c, hc, hμ⟩ := exists_measure_le_prod μ
  set p2 : AdelicGLn.AdelicGL K (m + 1) → AdelicGLn.FiniteAdelicGL K (m + 1) :=
    fun g => (AdelicGLn.prodEquiv K (m + 1) g).2 with hp2
  have hp2c : Continuous p2 := continuous_snd.comp (AdelicGLn.prodEquiv K (m + 1)).continuous
  set F : Set (AdelicGLn.FiniteAdelicGL K (m + 1)) :=
    (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := m + 1) : Set (AdelicGLn.AdelicGL K (m + 1)))) with hFdef
  have hF : IsCompact F := (hω.image hp2c).mul (isCompact_maxCompact.image hp2c)
  choose C hC hCb using fun w : InfinitePlace K =>
    measure_boxPlace_le w (Measure.haar : Measure (GL (Fin (m + 1)) w.Completion))
      (hω.image (continuous_infAt w))
      (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ((m + 1 : ℕ) : ℝ)
  set D : ℝ≥0∞ := c * ((∏ w, C w) * (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K (m + 1))) F) with hDdef
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top hc (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => hC w)
    hF.measure_lt_top.ne)
  refine ⟨D.toReal, fun x => ?_⟩
  have key : ∑ r ∈ Finset.range (m + 1), 2 * An.rho K (m + 1) r * An.sr x r =
      (Module.finrank ℚ K : ℝ) * pairSum m x := by
    rw [pairSum, sum_pairs_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [An.rho, An.sr]
    ring
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  rw [key]
  calc μ _ ≤ c * ((∏ w, (Measure.haar : Measure (GL (Fin (m + 1)) w.Completion))
        (boxPlace w (infAt w '' ω) ((m + 1 : ℕ) : ℝ) x)) *
        (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K (m + 1))) F) := by
        refine hμ _ _ _ fun g hg => ?_
        obtain ⟨b, hb, y, hy, k, hk, rfl⟩ := hg
        refine ⟨fun w => ⟨infAt w b, ⟨b, hb, rfl⟩, y, hy, infAt w k, hk.1 w, ?_⟩, ?_⟩
        · rw [infAt_mul, infAt_mul]
          congr 2
          exact infAt_diagUnits_posIdele w (fun i => Real.exp (x i + y i)) (fun i => Real.exp_pos _)
        · refine ⟨p2 b, ⟨b, hb, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩
          simp only [hp2, map_mul, Prod.snd_mul, An.tor]
          rw [prodEquiv_diagUnits_posIdele_snd (fun i => Real.exp ((x + y) i)) (fun i => Real.exp_pos _),
            mul_one]
    _ ≤ c * ((∏ w, (C w * ENNReal.ofReal (Real.exp (-((w.mult : ℝ) * pairSum m x))))) *
        (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K (m + 1))) F) := by
        gcongr with w
        exact hCb w x
    _ = D * ENNReal.ofReal (Real.exp (-((Module.finrank ℚ K : ℝ) * pairSum m x))) := by
        rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun w _ => (Real.exp_pos _).le),
          ← Real.exp_sum, ← hsum, Finset.sum_mul, ← Finset.sum_neg_distrib, hDdef]
        ring
    _ = ENNReal.ofReal (D.toReal * Real.exp (-((Module.finrank ℚ K : ℝ) * pairSum m x))) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD]

end PositivityTheory.Rg.Rs

end
