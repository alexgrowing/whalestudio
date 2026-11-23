import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open Filter
open scoped BigOperators Topology

namespace GlobalTheory.MultiMahler

variable {q : ℕ} [Fact q.Prime]

theorem fwdDiff_tendsto_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[q] E]
    [IsUltrametricDist E] (f : C(ℤ_[q], E)) :
    Tendsto (fun n => (fwdDiff (1 : ℤ_[q]))^[n] f 0) atTop (𝓝 0) := by
  letI : Module ℤ_[q] E := Module.compHom E (algebraMap ℤ_[q] ℚ_[q])
  haveI : IsBoundedSMul ℤ_[q] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[q]) x
  exact PadicInt.fwdDiff_tendsto_zero f

noncomputable def curryFirst {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    C(ℤ_[q], C(Fin g → ℤ_[q], ℂ_[q])) :=
  ContinuousMap.curry (F.comp ⟨fun x : ℤ_[q] × (Fin g → ℤ_[q]) => Fin.cons x.1 x.2,
    Continuous.finCons continuous_fst continuous_snd⟩)

theorem curryFirst_apply {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) (t : ℤ_[q])
    (a : Fin g → ℤ_[q]) : curryFirst F t a = F (Fin.cons t a) := rfl

theorem norm_curryFirst_le {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    ‖curryFirst F‖ ≤ ‖F‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro t
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro a
  exact F.norm_coe_le_norm _

noncomputable def diffFirst {g : ℕ} (m : ℕ) :
    C(Fin (g + 1) → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin g → ℤ_[q], ℂ_[q]) where
  toFun F := (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0
  map_add' F G := by
    have : (curryFirst (F + G) : ℤ_[q] → _) = curryFirst F + curryFirst G := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_add]; rfl
  map_smul' r F := by
    have : (curryFirst (r • F) : ℤ_[q] → _) = r • (curryFirst F : ℤ_[q] → _) := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_const_smul]; rfl

theorem diffFirst_apply {g : ℕ} (m : ℕ) (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    diffFirst m F = (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0 := rfl

theorem exists_multiDiff (g : ℕ) :
    ∃ D : (Fin g → ℕ) → C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q],
      (∀ n F, ‖D n F‖ ≤ ‖F‖) ∧
      (∀ n (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
        (∀ a, F a = ∏ i, f i (a i)) → D n F = ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) ∧
      (∀ F, Tendsto (fun n => D n F) cofinite (𝓝 0)) := by
  induction g with
  | zero =>
    refine ⟨fun _ => { toFun := fun F => F 0, map_add' := fun _ _ => rfl,
                       map_smul' := fun _ _ => rfl }, fun n F => F.norm_coe_le_norm _,
      fun n f F hF => by simpa using hF 0, fun F => ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact tendsto_bot
  | succ g ih =>
    obtain ⟨D, h1, h2, h3⟩ := ih
    refine ⟨fun n => (D (Fin.tail n)).comp (diffFirst (n 0)), fun n F => ?_,
      fun n f F hF => ?_, fun F => ?_⟩
    · exact (h1 _ _).trans ((IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 _ 0 _).trans
        (norm_curryFirst_le F))
    · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, f i.succ (a i), by fun_prop⟩
      have hP : diffFirst (n 0) F = (fwdDiff (1 : ℤ_[q]))^[n 0] (f 0) 0 • P := by
        rw [diffFirst_apply, fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift,
          Finset.sum_smul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_assoc]
        congr 1
        ext a
        simp [curryFirst_apply, hF, Fin.prod_univ_succ, P]
      rw [LinearMap.comp_apply, hP, map_smul, h2 _ (fun i => f i.succ) P (fun _ => rfl),
        Fin.prod_univ_succ]
      rfl
    · refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
      have hA := NormedAddGroup.tendsto_nhds_zero.mp (fwdDiff_tendsto_zero' (curryFirst F)) ε hε
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hA
      have hB : ∀ m, {n' : Fin g → ℕ | ¬ ‖D n' (diffFirst m F)‖ < ε}.Finite := fun m =>
        Filter.eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp (h3 _) ε hε)
      rw [Filter.eventually_cofinite]
      refine (hA.biUnion fun m _ => (hB m).image
        (fun n' => (Fin.cons m n' : Fin (g + 1) → ℕ))).subset fun n hn => ?_
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, not_lt] at hn ⊢
      exact ⟨n 0, hn.trans (h1 _ _), Fin.tail n, hn, Fin.cons_self_tail n⟩

noncomputable def binomC (k : ℕ) : C(ℤ_[q], ℂ_[q]) :=
  ⟨fun x => algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q]),
    (continuous_algebraMap _ _).comp (continuous_subtype_val.comp (mahler k).continuous)⟩

theorem norm_binomC_le (k : ℕ) (x : ℤ_[q]) : ‖binomC k x‖ ≤ 1 := by
  change ‖algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q])‖ ≤ 1
  rw [norm_algebraMap']
  exact PadicInt.norm_le_one _

theorem binomC_natCast (k n : ℕ) : binomC k (n : ℤ_[q]) = (n.choose k : ℂ_[q]) := by
  change algebraMap ℚ_[q] ℂ_[q] ((mahler k (n : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = _
  rw [mahler_natCast_eq, PadicInt.coe_natCast, map_natCast]

theorem fwdDiff_binomC (k m : ℕ) :
    (fwdDiff (1 : ℤ_[q]))^[m] (binomC (q := q) k) 0 = if m = k then 1 else 0 := by
  have h := fwdDiff_iter_choose_zero k m
  rw [fwdDiff_iter_eq_sum_shift] at h ⊢
  have h' := congrArg (Int.cast : ℤ → ℂ_[q]) h
  simp only [zero_add, nsmul_one, binomC_natCast] at h' ⊢
  simpa using h'

theorem exists_measure_of_bounded_moments :
    ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (c : (Fin g → ℕ) → ℂ_[q]), (∃ B : ℝ, ∀ n, ‖c n‖ ≤ B) →
      ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q],
        (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ n, ‖c n‖ ≤ B)) ∧
        ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
          (∀ a, F a = ∏ i, f i (a i)) →
          HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (μ F) := by
  intro q _ g c ⟨B₀, hB₀⟩
  obtain ⟨D, h1, h2, h3⟩ := exists_multiDiff (q := q) g
  have hs : ∀ F, Summable fun n => c n * D n F := fun F => by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_zero_iff_norm_tendsto_zero.mp (h3 F)).const_mul B₀
    rw [mul_zero] at this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) this
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB₀ n) (norm_nonneg _)
  let L : C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q] :=
    { toFun := fun F => ∑' n, c n * D n F
      map_add' := fun F G => by
        simp only [map_add, mul_add]
        exact (hs F).tsum_add (hs G)
      map_smul' := fun r F => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by ring }
  have hL : ∀ B : ℝ, (∀ n, ‖c n‖ ≤ B) → ∀ F, ‖L F‖ ≤ B * ‖F‖ := fun B hB F => by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
    rw [norm_mul]
    exact mul_le_mul (hB n) (h1 n F) (norm_nonneg _) ((norm_nonneg _).trans (hB n))
  have hsum : ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
      (∀ a, F a = ∏ i, f i (a i)) →
      HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (L F) := by
    intro f F hF
    have := (hs F).hasSum
    simp only [fun n => h2 n f F hF] at this
    convert this using 1
    exact tsum_congr fun n => by rw [h2 n f F hF]
  refine ⟨L.mkContinuous B₀ (hL B₀ hB₀), fun B hB => ⟨fun hμ n => ?_, fun h => ?_⟩, hsum⟩
  · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, binomC (n i) (a i), by fun_prop⟩
    have hP : ‖P‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro a
      change ‖∏ i, binomC (n i) (a i)‖ ≤ 1
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_binomC_le _ _
    have hv : L P = c n := by
      refine (hsum (fun i => binomC (n i)) P fun _ => rfl).unique ?_
      convert hasSum_single (f := fun m : Fin g → ℕ =>
        c m * ∏ i, (fwdDiff (1 : ℤ_[q]))^[m i] (binomC (q := q) (n i)) 0) n ?_ using 1
      · simp [fwdDiff_binomC]
      · intro m hm
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [fwdDiff_binomC, if_neg hi]), mul_zero]
    calc ‖c n‖ = ‖L.mkContinuous B₀ (hL B₀ hB₀) P‖ := by rw [← hv]; rfl
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * 1 := mul_le_mul hμ hP (norm_nonneg _) hB
      _ = B := mul_one _
  · exact ContinuousLinearMap.opNorm_le_bound _ hB (hL B h)

end GlobalTheory.MultiMahler
