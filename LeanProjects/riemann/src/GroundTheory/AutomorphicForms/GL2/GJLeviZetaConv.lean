import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLeviZetaBlocks
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (levi F n β)] [BorelSpace (levi F n β)]

theorem integral_eq_zero_of_cuspidal (hc : IsCuspidal σ) (μ : Measure (levi F n β))
    [μ.IsHaarMeasure] {i₀ j₀ : Fin n} (hij : β i₀ = β j₀) (hne : i₀ ≠ j₀)
    (ℓ : Module.Dual ℂ W) {G : levi F n β → ℂ}
    (hG : ∀ m u : levi F n β, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun {i₀}) →
      G (m * u) = G m)
    (hint : ∀ w' : W, Integrable (fun m => G m * ℓ (σ m w')) μ) (w : W) :
    ∫ m, G m * ℓ (σ m w) ∂μ = 0 := by
  let L : W →ₗ[ℂ] ℂ :=
    { toFun := fun w' => ∫ m, G m * ℓ (σ m w') ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hint x) (hint y)]
        congr 1
        funext m
        rw [map_add, map_add, mul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext m
        rw [map_smul, map_smul, smul_eq_mul]
        ring }
  have hinv : ∀ u : levi F n β, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun {i₀}) →
      ∀ x : W, L (σ u x - x) = 0 := by
    intro u hu x
    rw [map_sub, sub_eq_zero]
    show ∫ m, G m * ℓ (σ m (σ u x)) ∂μ = ∫ m, G m * ℓ (σ m x) ∂μ
    have e := map_mul_right_eq_self_of_mem_unipotentRadical μ hu
    have hfun : (fun m => G m * ℓ (σ m (σ u x))) = fun m => (fun m => G m * ℓ (σ m x)) (m * u) := by
      funext m
      show _ = G (m * u) * ℓ (σ (m * u) x)
      rw [hG m u hu, map_mul, Module.End.mul_apply]
    rw [hfun]
    have hmeas : AEMeasurable (· * u : levi F n β → levi F n β) μ :=
      (measurable_mul_const u).aemeasurable
    have h2 := integral_map hmeas (f := fun m => G m * ℓ (σ m x)) (by rw [e]; exact (hint x).1)
    rw [e] at h2
    exact h2.symm
  obtain ⟨U, hU, hwU⟩ := exists_finset_of_isCuspidal hc (S := {i₀})
    ⟨i₀, j₀, hij, Finset.mem_singleton_self _, by simpa using hne.symm⟩ w
  have hle : Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = σ u x - x} ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, x, rfl⟩
    exact hinv u (hU u hu) x
  exact hle hwU

theorem exists_blockChar (hσ : IsSmooth σ) [σ.IsIrreducible] :
    ∃ ω : Set.range β → ℂ, ∀ b v, σ (blockUnif F b) v = ω b • v := by
  choose ω hω using fun b : Set.range β =>
    exists_central_character hσ (blockUnif_mem_center (F := F) (β := β) b)
  exact ⟨ω, hω⟩

def coeffIntegrand (σ : Representation ℂ (levi F n β) W) (θ : levi F n β →* ℝ≥0) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) : ℂ :=
  (θ m : ℂ) * detPow (m : GL (Fin n) F) s * ℓ (σ m w)

theorem continuous_coeffIntegrand (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) : Continuous (coeffIntegrand σ θ w ℓ s) :=
  ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hθ)).mul
    (isLocallyConstant_detPow s).continuous).mul (isLocallyConstant_coeff hσ w ℓ).continuous

theorem detPow_blockUnif (b : Set.range β) (s : ℂ) :
    detPow ((blockUnif F b : levi F n β) : GL (Fin n) F) s = qs F s ^ blockSize β b := by
  rw [detPow_eq_qs_zpow, ordDet_blockUnif, zpow_natCast]

theorem coeffIntegrand_blockUnif_mul {ω : Set.range β → ℂ}
    (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) (θ : levi F n β →* ℝ≥0) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (b : Set.range β) (m : levi F n β) :
    coeffIntegrand σ θ w ℓ s (blockUnif F b * m) =
      ((θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b) * coeffIntegrand σ θ w ℓ s m := by
  simp only [coeffIntegrand]
  rw [map_mul, Subgroup.coe_mul, detPow_mul, detPow_blockUnif, map_mul, Module.End.mul_apply, hω,
    map_smul, smul_eq_mul, NNReal.coe_mul, Complex.ofReal_mul]
  ring

theorem coeffIntegrand_blockUnif_pow_mul {ω : Set.range β → ℂ}
    (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) (θ : levi F n β →* ℝ≥0) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (b : Set.range β) (j : ℕ) (m : levi F n β) :
    coeffIntegrand σ θ w ℓ s (blockUnif F b ^ j * m) =
      ((θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b) ^ j *
        coeffIntegrand σ θ w ℓ s m := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', mul_assoc, coeffIntegrand_blockUnif_mul hω, ih, pow_succ']; ring

theorem blockOrd_blockUnif_pow_inv_mul (b b' : Set.range β) (j : ℕ) (m : levi F n β) :
    blockOrd F b' ((blockUnif F b ^ j)⁻¹ * m) =
      blockOrd F b' m - if b' = b then (j : ℤ) * blockSize β b else 0 := by
  rw [blockOrd_mul, blockOrd_inv, blockOrd_pow, blockOrd_blockUnif]
  split_ifs <;> ring

theorem isLocallyConstant_blockOrds :
    IsLocallyConstant fun m : levi F n β => fun b : Set.range β => blockOrd F b m :=
  isLocallyConstant_of_forall_mul fun m => ⟨leviIntegral F n β, isOpen_leviIntegral, fun k hk => by
    funext b
    rw [blockOrd_mul, blockOrd_of_mem_integralGL b (Subgroup.mem_subgroupOf.1 hk), add_zero]⟩

theorem measurableSet_blockOrds (P : (Set.range β → ℤ) → Prop) :
    MeasurableSet {m : levi F n β | P fun b => blockOrd F b m} :=
  (isLocallyConstant_blockOrds (F := F) (β := β) {v | P v}).measurableSet

theorem exists_lintegral_lt_top (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ) (μ : Measure (levi F n β)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s : ℂ, s₀ < s.re → ∀ (w : W) (ℓ : Module.Dual ℂ W),
      ℓ ∈ smoothVectors (Representation.dual σ) → ∀ k : Set.range β → ℤ,
        ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
          (fun m => ‖coeffIntegrand σ θ w ℓ s m‖ₑ) m ∂μ < ⊤ := by
  classical
  obtain ⟨ω, hω⟩ := exists_blockChar (F := F) hσ
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  set A : ℝ := 1 + ∑ b, (θ (blockUnif F b) : ℝ) * ‖ω b‖ with hAdef
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun b _ => by positivity)
  have hs₀ : 0 ≤ Real.logb q A := Real.logb_nonneg hq hA
  refine ⟨Real.logb q A, hs₀, fun s hs w ℓ hℓ k => ?_⟩

  set c : Set.range β → ℂ := fun b => (θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b
    with hcdef
  have hqs : ‖qs F s‖ < A⁻¹ := by
    rw [norm_qs, ← hqdef]
    have h1 : q ^ (-s.re) < q ^ (-Real.logb q A) :=
      Real.rpow_lt_rpow_of_exponent_lt hq (neg_lt_neg hs)
    have h2 : q ^ (-Real.logb q A) = A⁻¹ := by
      rw [Real.rpow_neg (by linarith), Real.rpow_logb (by linarith) hq.ne' (by linarith)]
    exact h1.trans_eq h2
  have hqs1 : ‖qs F s‖ ≤ 1 := hqs.le.trans (inv_le_one_of_one_le₀ hA)
  have hc1 : ∀ b, ‖c b‖ < 1 := by
    intro b
    have hnb : 1 ≤ blockSize β b := blockSize_pos β b
    have hpow : ‖qs F s‖ ^ blockSize β b ≤ ‖qs F s‖ :=
      pow_le_of_le_one (norm_nonneg _) hqs1 (by omega)
    have hθω : (θ (blockUnif F b) : ℝ) * ‖ω b‖ ≤ A - 1 := by
      rw [hAdef, add_sub_cancel_left]
      exact Finset.single_le_sum (f := fun b => (θ (blockUnif F b) : ℝ) * ‖ω b‖)
        (fun b _ => by positivity) (Finset.mem_univ b)
    simp only [hcdef, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      NNReal.abs_eq]
    have hApos : 0 < A := by linarith
    calc (θ (blockUnif F b) : ℝ) * ‖ω b‖ * ‖qs F s‖ ^ blockSize β b
        ≤ (θ (blockUnif F b) : ℝ) * ‖ω b‖ * ‖qs F s‖ :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (A - 1) * A⁻¹ := mul_le_mul hθω hqs.le (norm_nonneg _) (by linarith)
      _ < 1 := by
          rw [sub_mul, mul_inv_cancel₀ hApos.ne']
          have : 0 < A⁻¹ := inv_pos.2 hApos
          linarith

  set g := coeffIntegrand σ θ w ℓ s with hgdef
  have hgc : Continuous g := continuous_coeffIntegrand hσ θ hθ w ℓ s
  have hgm : Measurable fun m => ‖g m‖ₑ := hgc.measurable.enorm
  let E : Finset (Set.range β) → Set (levi F n β) := fun S =>
    {m | (∀ b, k b ≤ blockOrd F b m) ∧ ∀ b ∉ S, blockOrd F b m < k b + blockSize β b}
  have hEm : ∀ S, MeasurableSet (E S) := fun S =>
    measurableSet_blockOrds (fun v => (∀ b, k b ≤ v b) ∧ ∀ b ∉ S, v b < k b + blockSize β b)
  have key : ∀ S, ∫⁻ m, (E S).indicator (fun m => ‖g m‖ₑ) m ∂μ < ⊤ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨C, hC, hmemC⟩ := exists_compact_of_coeff hσ hc w hℓ k
        (fun b => k b + blockSize β b)
      have hle : (E ∅).indicator (fun m => ‖g m‖ₑ) ≤ C.indicator fun m => ‖g m‖ₑ := by
        intro m
        by_cases hm : m ∈ E ∅
        · rw [Set.indicator_of_mem hm]
          by_cases hg : g m = 0
          · rw [hg, enorm_zero]
            exact zero_le
          · have hℓm : ℓ (σ m w) ≠ 0 := fun h => hg (by simp [hgdef, coeffIntegrand, h])
            rw [Set.indicator_of_mem (hmemC m hℓm fun b =>
              ⟨hm.1 b, (hm.2 b (Finset.notMem_empty b)).le⟩)]
        · rw [Set.indicator_of_notMem hm]
          exact zero_le
      refine (lintegral_mono hle).trans_lt ?_
      rw [lintegral_indicator hC.isClosed.measurableSet]
      have := setLIntegral_lt_top_of_isCompact (μ := μ) hC.measure_lt_top.ne hC
        (f := fun m => ‖g m‖₊) hgc.nnnorm
      simpa [enorm_eq_nnnorm] using this
    | insert b S hb ih =>
      have hρ : ‖c b‖ₑ < 1 := by
        rw [enorm_eq_nnnorm]
        exact_mod_cast (show ‖c b‖₊ < 1 from hc1 b)

      have hdec : ∀ m, (E (insert b S)).indicator (fun m => ‖g m‖ₑ) m =
          ∑' j : ℕ, {m : levi F n β | (blockUnif F b ^ j)⁻¹ * m ∈ E S}.indicator
            (fun m => ‖g m‖ₑ) m := by
        intro m
        have hnb : (0 : ℤ) < blockSize β b := by exact_mod_cast blockSize_pos β b
        have hmem : ∀ j : ℕ, (blockUnif F b ^ j)⁻¹ * m ∈ E S ↔
            (∀ b', b' ≠ b → k b' ≤ blockOrd F b' m) ∧
            (∀ b', b' ≠ b → b' ∉ S → blockOrd F b' m < k b' + blockSize β b') ∧
            k b ≤ blockOrd F b m - j * blockSize β b ∧
            blockOrd F b m - j * blockSize β b < k b + blockSize β b := by
          intro j
          simp only [E, Set.mem_ofPred_eq, blockOrd_blockUnif_pow_inv_mul]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨fun b' hb' => ?_, fun b' hb' hb'S => ?_, ?_, ?_⟩
            · simpa [hb'] using h1 b'
            · simpa [hb'] using h2 b' hb'S
            · simpa using h1 b
            · simpa using h2 b hb
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun b' => ?_, fun b' hb'S => ?_⟩
            · by_cases hb' : b' = b
              · subst hb'; simpa using h3
              · simpa [hb'] using h1 b' hb'
            · by_cases hb' : b' = b
              · subst hb'; simpa using h4
              · simpa [hb'] using h2 b' hb' hb'S
        have huniq : ∀ j j' : ℕ, (blockUnif F b ^ j)⁻¹ * m ∈ E S →
            (blockUnif F b ^ j')⁻¹ * m ∈ E S → j = j' := by
          intro j j' hj hj'
          obtain ⟨-, -, h3, h4⟩ := (hmem j).1 hj
          obtain ⟨-, -, h3', h4'⟩ := (hmem j').1 hj'
          have e1 : ((j : ℤ) - j' - 1) * blockSize β b < 0 := by nlinarith
          have e2 : ((j' : ℤ) - j - 1) * blockSize β b < 0 := by nlinarith
          have f1 : (j : ℤ) - j' - 1 < 0 := by
            by_contra h
            exact absurd e1 (not_lt.2 (mul_nonneg (not_lt.1 h) hnb.le))
          have f2 : (j' : ℤ) - j - 1 < 0 := by
            by_contra h
            exact absurd e2 (not_lt.2 (mul_nonneg (not_lt.1 h) hnb.le))
          omega
        by_cases hm : m ∈ E (insert b S)
        · rw [Set.indicator_of_mem hm]
          have hvb : k b ≤ blockOrd F b m := hm.1 b
          set d : ℤ := blockOrd F b m - k b with hd
          have hd0 : 0 ≤ d := by omega
          have hqd : 0 ≤ d / blockSize β b := Int.ediv_nonneg hd0 hnb.le
          have hmod := Int.emod_def d (blockSize β b)
          have hr0 := Int.emod_nonneg d hnb.ne'
          have hr1 := Int.emod_lt_of_pos d hnb
          set j₀ : ℕ := (d / blockSize β b).toNat with hj₀
          have hj₀' : ((j₀ : ℕ) : ℤ) = d / blockSize β b := Int.toNat_of_nonneg hqd
          have hP : (blockUnif F b ^ j₀)⁻¹ * m ∈ E S := by
            refine (hmem j₀).2 ⟨fun b' hb' => hm.1 b', fun b' hb' hb'S => hm.2 b' ?_, ?_, ?_⟩
            · simp [hb', hb'S]
            · rw [hj₀']; nlinarith
            · rw [hj₀']; nlinarith
          have hz : ∀ j ≠ j₀, {m : levi F n β | (blockUnif F b ^ j)⁻¹ * m ∈ E S}.indicator
              (fun m => ‖g m‖ₑ) m = 0 := fun j hj =>
            Set.indicator_of_notMem (s := {m : levi F n β | (blockUnif F b ^ j)⁻¹ * m ∈ E S})
              (fun h => hj (huniq j j₀ h hP)) _
          rw [tsum_eq_single j₀ hz, Set.indicator_of_mem
            (show m ∈ {m : levi F n β | (blockUnif F b ^ j₀)⁻¹ * m ∈ E S} from hP)]
        · rw [Set.indicator_of_notMem hm]
          symm
          refine ENNReal.tsum_eq_zero.2 fun j => Set.indicator_of_notMem
            (s := {m : levi F n β | (blockUnif F b ^ j)⁻¹ * m ∈ E S}) (fun h => hm ?_) _
          obtain ⟨h1, h2, h3, -⟩ := (hmem j).1 h
          refine ⟨fun b' => ?_, fun b' hb' => ?_⟩
          · by_cases hb' : b' = b
            · subst hb'
              have : (0 : ℤ) ≤ j * blockSize β b' := by positivity
              linarith
            · exact h1 b' hb'
          · exact h2 b' (fun e => hb' (e ▸ Finset.mem_insert_self _ _))
              (fun e => hb' (Finset.mem_insert_of_mem e))
      rw [lintegral_congr fun m => hdec m]
      rw [lintegral_tsum fun j => ((hgm.indicator (show MeasurableSet
        {m : levi F n β | (blockUnif F b ^ j)⁻¹ * m ∈ E S} from
          (hEm S).preimage (measurable_const_mul _))).aemeasurable)]
      have hterm : ∀ j : ℕ, ∫⁻ m, {m : levi F n β | (blockUnif F b ^ j)⁻¹ * m ∈ E S}.indicator
          (fun m => ‖g m‖ₑ) m ∂μ = ‖c b‖ₑ ^ j * ∫⁻ m, (E S).indicator (fun m => ‖g m‖ₑ) m ∂μ := by
        intro j
        rw [← lintegral_mul_left_eq_self _ (blockUnif F b ^ j), ← lintegral_const_mul _
          ((hgm.indicator (hEm S)))]
        refine lintegral_congr fun m => ?_
        simp only [Set.indicator, Set.mem_ofPred_eq, inv_mul_cancel_left]
        split_ifs
        · rw [hgdef, coeffIntegrand_blockUnif_pow_mul hω, enorm_mul, enorm_pow]
        · rw [mul_zero]
      simp_rw [hterm]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ)) ih
  have h := key Finset.univ
  have hEu : E Finset.univ = {m : levi F n β | ∀ b, k b ≤ blockOrd F b m} := by
    ext m
    simp [E]
  rwa [hEu] at h

end GodementJacquet

end GroundTheory.Automorphic
