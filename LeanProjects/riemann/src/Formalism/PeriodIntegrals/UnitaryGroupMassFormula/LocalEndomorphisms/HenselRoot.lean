import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective

open NumberField IsDedekindDomain Polynomial Filter Topology

namespace PI.LocalEndW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem norm_le_one_of_mem (a : v.adicCompletionIntegers F) : ‖(a : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr a.2

theorem mem_pow_smul_top_iff (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0) (n : ℕ)
    (x : v.adicCompletionIntegers F) :
    x ∈ ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F)) ↔
      ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers (K := F) (v := v)).dvd_iff_le, ← norm_pow,
    Valued.toNormedField.norm_le_iff]
  simp

theorem isAdicComplete (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0)
    (h1 : ‖(ϖ : v.adicCompletion F)‖ < 1) :
    IsAdicComplete (Ideal.span {ϖ}) (v.adicCompletionIntegers F) := by
  have hr0 : 0 < ‖(ϖ : v.adicCompletion F)‖ := norm_pos_iff.mpr (fun h => hϖ (Subtype.ext h))
  have key : ∀ (n : ℕ) (x y : v.adicCompletionIntegers F),
      x ≡ y [SMOD ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F))] ↔
        ‖(x : v.adicCompletion F) - y‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, mem_pow_smul_top_iff v ϖ hϖ]
    simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h : ∀ n : ℕ, ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := fun n => by
      simpa using (key n x 0).mp (hx n)
    have hx0 : ‖(x : v.adicCompletion F)‖ ≤ 0 :=
      ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le h1) h
    exact Subtype.ext (norm_le_zero_iff.mp hx0)
  · intro f hf
    have hc : ∀ n : ℕ, dist (f n : v.adicCompletion F) (f (n + 1)) ≤ 1 * ‖(ϖ : v.adicCompletion F)‖ ^ n := fun n => by
      rw [dist_eq_norm, one_mul]
      exact (key n _ _).mp (hf n.le_succ)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 h1 hc)
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm (fun n => norm_le_one_of_mem v (f n))
    refine ⟨⟨L, Valued.toNormedField.norm_le_one_iff.mp hL1⟩, fun n => ?_⟩
    rw [key]
    have ht : Tendsto (fun m => ‖(f n : v.adicCompletion F) - f m‖) atTop (𝓝 ‖(f n : v.adicCompletion F) - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)

theorem henselRoot : HenselRoot := by
  intro F _ _ v ℓ u hℓ hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have hϖ1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    have hnu : ¬ IsUnit ϖ := hϖ.not_isUnit
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    exact lt_of_le_of_ne ϖ.2 hnu
  have := isAdicComplete v ϖ hϖ.ne_zero hϖ1
  have hu1 : Valued.v u ≤ 1 := by
    have hsplit : u = (u - 1) + 1 := by ring
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le hu.le (by simp))
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ
  have hev : ((X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F))).eval 1 ∈ Ideal.span {ϖ} := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have h' : Valued.v (u - 1) = 1 := by
      rw [← Valuation.map_neg]
      simpa using h
    exact hu.ne h'
  have hdu : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ}) ((derivative (X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F))).eval 1)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X, one_pow, mul_one]
    apply IsUnit.map
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    simpa using hℓ
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ})
    (X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F)) (monic_X_pow_sub_C _ hℓ0) 1 hev hdu
  refine ⟨a, ?_⟩
  have ha' : a ^ ℓ = (⟨u, hu1⟩ : v.adicCompletionIntegers F) := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using ha
  simpa using congrArg Subtype.val ha'

end PI.LocalEndW
