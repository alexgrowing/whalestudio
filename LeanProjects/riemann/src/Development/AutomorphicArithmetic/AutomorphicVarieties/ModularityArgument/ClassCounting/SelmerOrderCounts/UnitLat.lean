import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

open scoped Classical in

private noncomputable def extS (F : Type) [Field F] [NumberField F] :
    logSpace F →ₗ[ℝ] (InfinitePlace F → ℝ) where
  toFun y w := if h : w = w₀ then -(∑ v, y v) / 2 else y ⟨w, h⟩ / 2
  map_add' y z := by
    ext w
    by_cases h : w = w₀
    · simp only [h, dif_pos, Pi.add_apply, Finset.sum_add_distrib]; ring
    · simp only [h, dif_neg, not_false_eq_true, Pi.add_apply]; ring
  map_smul' c y := by
    ext w
    by_cases h : w = w₀
    · simp only [h, dif_pos, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring
    · simp only [h, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem mult_two {F : Type} [Field F] [IsTotallyComplex F] (w : InfinitePlace F) :
    (mult w : ℝ) = 2 := by
  rw [show mult w = 2 from mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩]
  norm_num

private theorem extS_log {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (u : (𝓞 F)ˣ)
    (w : InfinitePlace F) :
    extS F (logEmbedding F (Additive.ofMul u)) w = Real.log (w ((u : 𝓞 F) : F)) := by
  classical
  by_cases h : w = w₀
  · subst h
    simp only [extS, LinearMap.coe_mk, AddHom.coe_mk, dif_pos rfl, logEmbedding_component, mult_two, dite_true]
    have hs := NumberField.Units.sum_mult_mul_log u
    have e : (algebraMap (𝓞 F) F) (u : 𝓞 F) = ((u : 𝓞 F) : F) := rfl
    simp only [mult_two, e] at hs
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hs
    rw [← Finset.mul_sum] at hs ⊢
    linarith
  · simp only [extS, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, logEmbedding_component, mult_two]
    ring

private theorem sum_log {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (u : (𝓞 F)ˣ) :
    ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) = 0 := by
  have h := NumberField.Units.sum_mult_mul_log u
  simp only [mult_two, ← Finset.mul_sum, mul_eq_zero, two_ne_zero, false_or] at h
  exact h

private theorem abs_le_of_bound {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (u : (𝓞 F)ˣ) (m r : ℝ) (h : ∀ w : InfinitePlace F, |Real.log (w ((u : 𝓞 F) : F)) + m| ≤ r) :
    |m| ≤ r := by
  have hN : (0 : ℝ) < Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ w : InfinitePlace F, (Real.log (w ((u : 𝓞 F) : F)) + m)
      = Fintype.card (InfinitePlace F) * m := by
    rw [Finset.sum_add_distrib, sum_log, zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : |(Fintype.card (InfinitePlace F) : ℝ) * m| ≤ Fintype.card (InfinitePlace F) * r := by
    rw [← hsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : InfinitePlace F, |Real.log (w ((u : 𝓞 F) : F)) + m|
        ≤ ∑ _w : InfinitePlace F, r := Finset.sum_le_sum (fun w _ => h w)
      _ = Fintype.card (InfinitePlace F) * r := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [abs_mul, abs_of_pos hN] at h1
  exact le_of_mul_le_mul_left h1 hN

private theorem extS_surj {F : Type} [Field F] [NumberField F] (v : InfinitePlace F → ℝ) :
    ∃ (y : logSpace F) (c : ℝ), v = extS F y + c • (fun _ => (1 : ℝ)) := by
  classical
  have hN : (0 : ℝ) < Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  refine ⟨fun w => 2 * (v w.1 - (∑ x, v x) / Fintype.card (InfinitePlace F)),
    (∑ x, v x) / Fintype.card (InfinitePlace F), ?_⟩
  have hNc : (Fintype.card (InfinitePlace F) : ℝ) * ((∑ x, v x) / Fintype.card (InfinitePlace F))
      = ∑ x, v x := by
    field_simp
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, extS, LinearMap.coe_mk,
    AddHom.coe_mk]
  split_ifs with h
  · subst h
    have h1 := Fintype.sum_eq_add_sum_subtype_ne v w₀
    have h2 := Fintype.sum_eq_add_sum_subtype_ne
      (fun _ : InfinitePlace F => (∑ x, v x) / Fintype.card (InfinitePlace F)) w₀
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  · ring

end

theorem UpperTheory.V.ZK.Ct.unitLat :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyComplex F → ∀ lam : Additive (𝓞 F)ˣ × ℤ →ₗ[ℤ] (InfinitePlace F → ℝ), (∀ (u : (𝓞 F)ˣ) (m : ℤ) (w : InfinitePlace F), lam (Additive.ofMul u, m) w = Real.log (w ((u : 𝓞 F) : F)) + m) → LinearMap.ker lam = Submodule.torsion ℤ _ ∧ DiscreteTopology (LinearMap.range lam) ∧ Submodule.span ℝ (LinearMap.range lam : Set (InfinitePlace F → ℝ)) = ⊤ := by
  open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace in (
    classical
    intro F _ _ hF lam hlam
    haveI := hF
    have hlam' : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ),
        lam (x, m) = extS F (logEmbedding F x) + (m : ℝ) • (fun _ => (1 : ℝ)) := by
      intro x m
      funext w
      have h1 := hlam (Additive.toMul x) m w
      rw [ofMul_toMul] at h1
      rw [h1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, ← extS_log (Additive.toMul x) w,
        ofMul_toMul]
    have hcomp : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ) (w : InfinitePlace F),
        lam (x, m) w = Real.log (w (((Additive.toMul x : (𝓞 F)ˣ) : 𝓞 F) : F)) + m := by
      intro x m w
      have h1 := hlam (Additive.toMul x) m w
      rwa [ofMul_toMul] at h1
    have hm0 : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ) (r : ℝ), r < 1 →
        (∀ w, |lam (x, m) w| ≤ r) → m = 0 := by
      intro x m r hr h
      have hb := abs_le_of_bound (Additive.toMul x) (m : ℝ) r (fun w => by rw [← hcomp]; exact h w)
      have : |m| < 1 := by
        have : ((|m| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; linarith
        exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨a, m⟩
      rw [LinearMap.mem_ker]
      constructor
      · intro hx
        have hm : m = 0 := hm0 a m 0 (by norm_num) (fun w => by rw [hx]; simp)
        subst hm
        have hlog : logEmbedding F a = 0 := by
          funext w
          have h2 := hcomp a 0 w.1
          rw [hx] at h2
          simp only [Pi.zero_apply, Int.cast_zero, add_zero] at h2
          have h3 := logEmbedding_component (Additive.toMul a) w
          rw [ofMul_toMul] at h3
          rw [h3, ← h2, mul_zero, Pi.zero_apply]
        have ht : Additive.toMul a ∈ torsion F := by
          rw [← logEmbedding_eq_zero_iff, ofMul_toMul]
          exact hlog
        obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp ht)
        have hne : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
        refine (Submodule.mem_torsion_iff _).mpr ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero hne⟩, ?_⟩
        rw [Submonoid.smul_def]
        show (n : ℤ) • (a, (0 : ℤ)) = 0
        rw [Prod.smul_mk, Prod.mk_eq_zero]
        refine ⟨?_, by simp⟩
        apply Additive.toMul.injective
        rw [toMul_zsmul, zpow_natCast, hpow, toMul_zero]
      · intro hx
        obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).mp hx
        rw [Submonoid.smul_def] at hc
        have h1 := congrArg lam hc
        rw [map_smul, map_zero] at h1
        exact (smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero c)
    · have hd : IsOpen ({0} : Set (unitLattice F)) := isOpen_discrete _
      obtain ⟨ε, hε, hεz⟩ := (Metric.isOpen_singleton_iff (α := unitLattice F) (x := 0)).mp hd
      refine discreteTopology_of_isOpen_singleton_zero
        (Metric.isOpen_singleton_iff.mpr ⟨min (1 / 2) (ε / 2), by positivity, ?_⟩)
      rintro ⟨_, ⟨⟨a, m⟩, rfl⟩⟩ hy
      have hpos : (0 : ℝ) < min (1 / 2) (ε / 2) := by positivity
      have hy' : ‖lam (a, m)‖ < min (1 / 2) (ε / 2) := by
        rw [← dist_zero_right]
        exact hy
      have hw : ∀ w, |lam (a, m) w| < min (1 / 2) (ε / 2) := by
        intro w
        rw [← Real.norm_eq_abs]
        exact (pi_norm_lt_iff hpos).mp hy' w
      have hm : m = 0 := hm0 a m (1 / 2) (by norm_num)
        (fun w => (hw w).le.trans (min_le_left _ _))
      subst hm
      have hsmall : ∀ w : {w : InfinitePlace F // w ≠ w₀}, |logEmbedding F a w| < ε := by
        intro w
        have h3 := logEmbedding_component (Additive.toMul a) w
        rw [ofMul_toMul] at h3
        have h4 := hcomp a 0 w.1
        simp only [Int.cast_zero, add_zero] at h4
        rw [h3, mult_two, ← h4, abs_mul]
        have := (hw w.1).trans_le (min_le_right _ _)
        norm_num
        linarith
      have hmem : logEmbedding F a ∈ unitLattice F := ⟨a, Submodule.mem_top, rfl⟩
      have hz := hεz ⟨logEmbedding F a, hmem⟩ (by
        rw [dist_zero_right]
        exact (pi_norm_lt_iff hε).mpr (fun w => by rw [Real.norm_eq_abs]; exact hsmall w))
      have hlog : logEmbedding F a = 0 := congrArg Subtype.val hz
      apply Subtype.ext
      show lam (a, 0) = 0
      rw [hlam', hlog, map_zero]
      simp
    · rw [eq_top_iff]
      intro v _
      obtain ⟨y, c, rfl⟩ := extS_surj v
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ c (Submodule.subset_span ⟨(0, 1), ?_⟩))
      · have hy : y ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F)) := by
          rw [unitLattice_span_eq_top]
          trivial
        have hle : Submodule.map (extS F) (Submodule.span ℝ (unitLattice F : Set (logSpace F)))
            ≤ Submodule.span ℝ (LinearMap.range lam : Set (InfinitePlace F → ℝ)) := by
          rw [Submodule.map_span]
          apply Submodule.span_mono
          rintro _ ⟨_, ⟨a, _, rfl⟩, rfl⟩
          exact ⟨(a, 0), by rw [hlam']; simp⟩
        exact hle ⟨y, hy, rfl⟩
      · rw [hlam']
        simp)
