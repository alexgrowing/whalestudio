import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCartanDoubleCosetShellIntegrandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanDoubleCosetFiniteDisjointLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeftCosetShellIntegrandEqZeroStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section
namespace GlobalTheory.ShellVan
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

theorem valuation_unif_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℤ) : valuation k ((ϖ ^ m : kˣ) : k) = uniformizer k ^ m := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]

theorem shell_eq_zero_of_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    (φ : Matrix (Fin a) (Fin a) k → ℂ) (M' : ℕ), Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
    ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ φ M' hS n hn z
  push_neg at hn
  obtain ⟨i, hi⟩ := hn
  rw [shell]
  refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  suffices h : φ (x * diagGL (fun i => ϖ ^ n i) * y).val = 0 by rw [h, zero_mul, zero_mul]
  by_contra hne
  have hmem := hS hne
  have hd : (diagGL (fun i => ϖ ^ n i)).val =
      (x⁻¹).val * (x * diagGL (fun i => ϖ ^ n i) * y).val * (y⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hx' := ((mem_KO_iff x).1 hx).2
  have hy' := ((mem_KO_iff y).1 hy).2
  have bound : ∀ r s, valuation k ((diagGL (fun i => ϖ ^ n i)).val r s) ≤
      valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) := by
    intro r s
    rw [hd, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun t _ => ?_
    rw [map_mul, Matrix.mul_apply]
    calc _ ≤ valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) * 1 :=
          mul_le_mul' (Valuation.map_sum_le _ fun q _ => by
            rw [map_mul]
            exact (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (hx' r q))).trans (hmem q t))
            ((Valuation.mem_integer_iff _ _).1 (hy' t s))
      _ = _ := mul_one _
  have h1 := bound i i
  simp only [diagGL_val, diagonal_apply_eq] at h1
  rw [valuation_unif_zpow hϖ, valuation_unif_zpow hϖ] at h1
  have hu0 : (0 : ValueGroupWithZero k) < uniformizer k := zero_lt_iff.2 uniformizer_ne_zero
  have h2 := (zpow_le_zpow_iff_right_of_lt_one₀ hu0 uniformizer_lt_one).1 h1
  omega

theorem shell_lemma : ShellLemma := by
  intro k _ _ _ _ _ _ ϖ hϖ ν e hram hcond a μ hμ φ hφ
  have : μ.IsHaarMeasure := hμ
  have hint := GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand k ϖ ν e hcond a μ φ hφ
  have h2 : ∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
    rintro M hM n ⟨i, hi⟩ z
    obtain ⟨u, hu1, hu2⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hram h
    obtain ⟨t, htK, heq, hdisj⟩ := GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets k ϖ a n
    rw [shell, heq, integral_biUnion_finset t]
    · exact Finset.sum_eq_zero fun x hx =>
        GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero k ϖ hϖ ν a μ φ M hM n i hi u hu1 hu2 x (htK x hx) z
    · intro x _
      exact (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
    · exact hdisj
    · intro x hx
      refine (hint n z).mono_set ?_
      rw [heq]
      exact Set.subset_biUnion_of_mem (u := fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) hx
  have h3 := shell_eq_zero_of_support k ϖ hϖ ν a μ φ
  refine ⟨hint, h2, h3, ?_⟩
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin a) φ hφ
  have hP : IsPeriodic ϖ (M : ℤ) φ := fun X Z hZ => hM X Z fun i j => by
    have := hZ i j
    rwa [valuation_unif_zpow hϖ] at this
  have hS : Function.support φ ⊆ scaledInt ϖ a (-(N : ℤ)) := fun X hX i j => by
    rw [valuation_unif_zpow hϖ]
    exact hN X hX i j
  refine ((Set.Finite.pi (t := fun _ : Fin a => Set.Ico (-(N : ℤ)) M) fun _ => Set.finite_Ico _ _).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro ⟨n, hn⟩ ⟨z, hz⟩ i -
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hz (h3 N hS n (fun h' => h (h' i)) z)
  · by_contra h
    exact hz (h2 M hP n ⟨i, not_lt.1 h⟩ z)

end GlobalTheory.ShellVan
