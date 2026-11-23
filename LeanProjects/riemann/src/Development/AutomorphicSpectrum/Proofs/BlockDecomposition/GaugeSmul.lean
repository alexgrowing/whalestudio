import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteGlobalStability.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GaugeSpanK

open Ad3 Ad3.K Ad3.K.GPK

variable {K : Type} [Field K] [NumberField K]

def bnd (y : FiniteAdeleRing (𝓞 K) K) : ℝ := ∏ᶠ v : PlK K, max ‖y v‖ 1

theorem norm_le_one_of_mem {v : PlK K} {x : Kv K v} (h : x ∈ v.adicCompletionIntegers K) : ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 h)

theorem finite_mulSupport_bnd (y : FiniteAdeleRing (𝓞 K) K) :
    (Function.mulSupport fun v : PlK K => max ‖y v‖ 1).Finite := by
  have h : ∀ᶠ v : PlK K in cofinite, max ‖y v‖ 1 = 1 := by
    filter_upwards [y.2] with v hv
    exact max_eq_right (norm_le_one_of_mem hv)
  exact Filter.eventually_cofinite.1 h

theorem one_le_bnd (y : FiniteAdeleRing (𝓞 K) K) : 1 ≤ bnd y := by
  rw [bnd, finprod_eq_prod _ (finite_mulSupport_bnd y)]
  exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun v _ => le_max_right _ _

theorem local_le {v : PlK K} (x y : Kv K v) (h : y - x ∈ v.adicCompletionIntegers K) :
    max ‖y‖ 1 ≤ max ‖x‖ 1 := by
  have h1 : ‖y - x‖ ≤ 1 := norm_le_one_of_mem h
  have h2 : ‖y‖ ≤ max ‖x‖ ‖y - x‖ := by
    have := IsUltrametricDist.norm_add_le_max x (y - x)
    simpa using this
  refine max_le (h2.trans (max_le (le_max_left _ _) (h1.trans (le_max_right _ _)))) (le_max_right _ _)

theorem bnd_le (x y : FiniteAdeleRing (𝓞 K) K) (h : ∀ v : PlK K, y v - x v ∈ v.adicCompletionIntegers K) :
    bnd y ≤ bnd x := by
  classical
  set S := (finite_mulSupport_bnd x).toFinset ∪ (finite_mulSupport_bnd y).toFinset with hS
  rw [bnd, bnd, finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS]),
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
  exact Finset.prod_le_prod (fun v _ => by positivity) fun v _ => local_le _ _ (h v)

theorem finiteModule_le_bnd (a : IdeleGroup K) : IdeleGroup.finiteModule a ≤ bnd (a : 𝔸[K]).2 := by
  classical
  set S := (IdeleGroup.finite_mulSupport_norm a).toFinset ∪
    (finite_mulSupport_bnd (a : 𝔸[K]).2).toFinset with hS
  rw [IdeleGroup.finiteModule, bnd, finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS]),
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => le_max_left _ _

theorem nhds_mem (x : FiniteAdeleRing (𝓞 K) K) :
    {y : FiniteAdeleRing (𝓞 K) K | ∀ v : PlK K, y v - x v ∈ v.adicCompletionIntegers K} ∈ 𝓝 x := by
  have ho : IsOpen {z : FiniteAdeleRing (𝓞 K) K | ∀ v : PlK K, z v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 K) K => y - x := continuous_id.sub continuous_const
  refine (ho.preimage hc).mem_nhds ?_
  intro v
  simp only [sub_self]
  exact zero_mem (v.adicCompletionIntegers K)

theorem bnd_bdd (Ω : Set (FiniteAdeleRing (𝓞 K) K)) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ Ω, bnd y ≤ B := by
  refine hΩ.induction_on (p := fun S => ∃ B : ℝ, 0 < B ∧ ∀ y ∈ S, bnd y ≤ B)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨B, hB, h⟩
    exact ⟨B, hB, fun y hy => h y (hst hy)⟩
  · rintro s t ⟨B, hB, h⟩ ⟨B', _, h'⟩
    refine ⟨max B B', lt_max_of_lt_left hB, ?_⟩
    rintro y (hy | hy)
    · exact (h y hy).trans (le_max_left _ _)
    · exact (h' y hy).trans (le_max_right _ _)
  · intro x _
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (nhds_mem x), bnd x, lt_of_lt_of_le one_pos (one_le_bnd x), ?_⟩
    intro y hy
    exact bnd_le x y hy

theorem module_le (Ω : Set (FiniteAdeleRing (𝓞 K) K)) (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : IdeleGroup K, (a : 𝔸[K]).2 ∈ Ω →
      (IdeleGroup.ideleModule K a : ℝ) ≤ B * ∏ w : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w‖) ^ w.mult := by
  obtain ⟨B, hB, h⟩ := bnd_bdd Ω hΩ
  refine ⟨B, hB, fun a ha => ?_⟩
  rw [IdeleGroup.ideleModule_apply, mul_comm]
  have h1 := (finiteModule_le_bnd a).trans (h _ ha)
  have h2 : IdeleGroup.infiniteModule a ≤ ∏ w : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w‖) ^ w.mult := by
    refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  exact mul_le_mul h1 h2 (IdeleGroup.infiniteModule_pos a).le hB.le

theorem prod_le_pow (f : InfinitePlace K → ℝ) (M : ℝ) (h0 : ∀ w, 0 ≤ f w) (hM : ∀ w, f w ≤ M) :
    ∏ w : InfinitePlace K, f w ^ w.mult ≤ M ^ ∑ w : InfinitePlace K, w.mult := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg (h0 w) _) fun w _ => pow_le_pow_left₀ (h0 w) (hM w) _

def GaugeAt (W : G3K K → ℂ) (Ω : Set (FiniteAdeleRing (𝓞 K) K)) (T : ℕ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[K])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup (G3K K)), ∀ w : InfinitePlace K,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b) ^ T /
        ((1 + ‖(a : 𝔸[K]).1 w‖) * (1 + ‖(b : 𝔸[K]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[K]).2 ∈ Ω ∧ (b : 𝔸[K]).2 ∈ Ω)

theorem real_step (C A P Q : ℝ) (T d e N : ℕ) (hA : 0 < A) (hP : 0 < P) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (h : A ≤ Q * P ^ e) : C / A ^ T / P ^ (N + e * d) ≤ C * Q ^ d / A ^ (T + d) / P ^ N := by
  have h1 : A ^ d ≤ Q ^ d * P ^ (e * d) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hA.le h d
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 0 ≤ C * (A ^ T * P ^ N) := by positivity
  calc C * (A ^ (T + d) * P ^ N) = C * (A ^ T * P ^ N) * A ^ d := by ring
    _ ≤ C * (A ^ T * P ^ N) * (Q ^ d * P ^ (e * d)) := mul_le_mul_of_nonneg_left h1 h2
    _ = C * Q ^ d * (A ^ T * P ^ (N + e * d)) := by ring

theorem module_mul_le {B : ℝ} (hB : 0 < B) (a b : IdeleGroup K) (w : InfinitePlace K)
    (hmax : ∀ w' : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w'‖) * (1 + ‖(b : 𝔸[K]).1 w'‖) ≤
      (1 + ‖(a : 𝔸[K]).1 w‖) * (1 + ‖(b : 𝔸[K]).1 w‖))
    (ha : (IdeleGroup.ideleModule K a : ℝ) ≤ B * ∏ w : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w‖) ^ w.mult)
    (hb : (IdeleGroup.ideleModule K b : ℝ) ≤ B * ∏ w : InfinitePlace K, (1 + ‖(b : 𝔸[K]).1 w‖) ^ w.mult) :
    (IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b ≤
      B * B * ((1 + ‖(a : 𝔸[K]).1 w‖) * (1 + ‖(b : 𝔸[K]).1 w‖)) ^ ∑ w : InfinitePlace K, w.mult := by
  have hp := prod_le_pow (fun w' : InfinitePlace K => (1 + ‖(a : 𝔸[K]).1 w'‖) * (1 + ‖(b : 𝔸[K]).1 w'‖))
    _ (fun w' => by positivity) hmax
  simp only [mul_pow, Finset.prod_mul_distrib] at hp
  rw [mul_pow]
  have hb0 : 0 ≤ ∏ w : InfinitePlace K, (1 + ‖(b : 𝔸[K]).1 w‖) ^ w.mult :=
    Finset.prod_nonneg fun w _ => by positivity
  have ha0 : 0 ≤ ∏ w : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w‖) ^ w.mult :=
    Finset.prod_nonneg fun w _ => by positivity
  calc (IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b
      ≤ (B * ∏ w : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w‖) ^ w.mult) *
          (B * ∏ w : InfinitePlace K, (1 + ‖(b : 𝔸[K]).1 w‖) ^ w.mult) :=
        mul_le_mul ha hb (IdeleGroup.ideleModule K b).2.le (by positivity)
    _ = B * B * ((∏ w : InfinitePlace K, (1 + ‖(a : 𝔸[K]).1 w‖) ^ w.mult) *
          ∏ w : InfinitePlace K, (1 + ‖(b : 𝔸[K]).1 w‖) ^ w.mult) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem GaugeAt.mono {W : G3K K → ℂ} {Ω Ω' : Set (FiniteAdeleRing (𝓞 K) K)} {T T' : ℕ}
    (h : GaugeAt W Ω T) (hΩ : IsCompact Ω) (hs : Ω ⊆ Ω') (hT : T ≤ T') : GaugeAt W Ω' T' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT
  obtain ⟨B, hB, hmod⟩ := module_le Ω hΩ
  intro N
  obtain ⟨C, hC⟩ := h (N + (∑ w : InfinitePlace K, w.mult) * d)
  refine ⟨max C 0 * (B * B) ^ d, fun a b k hk w => ?_⟩
  obtain ⟨u, hu⟩ := Finite.exists_max
    fun w' : InfinitePlace K => (1 + ‖(a : 𝔸[K]).1 w'‖) * (1 + ‖(b : 𝔸[K]).1 w'‖)
  obtain ⟨h1, h2⟩ := hC a b k hk u
  have hA : 0 < (IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b :=
    mul_pos (IdeleGroup.ideleModule K a).2 (IdeleGroup.ideleModule K b).2
  have hPw : 0 < (1 + ‖(a : 𝔸[K]).1 w‖) * (1 + ‖(b : 𝔸[K]).1 w‖) := by positivity
  have hP : 0 < (1 + ‖(a : 𝔸[K]).1 u‖) * (1 + ‖(b : 𝔸[K]).1 u‖) := by positivity
  refine ⟨?_, fun hne => ⟨hs (h2 hne).1, hs (h2 hne).2⟩⟩
  by_cases h0 : W (dg (a * b) b 1 * k) = 0
  · rw [h0, norm_zero]
    have : 0 ≤ max C 0 := le_max_right _ _
    positivity
  · obtain ⟨ha, hb⟩ := h2 h0
    have hle := module_mul_le hB a b u hu (hmod a ha) (hmod b hb)
    have hstep := real_step (max C 0) _ _ (B * B) T d _ N hA hP (le_max_right _ _) (by positivity) hle
    have hnum : 0 ≤ max C 0 * (B * B) ^ d /
        ((IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b) ^ (T + d) := by
      have : 0 ≤ max C 0 := le_max_right _ _
      positivity
    refine h1.trans (le_trans ?_ (hstep.trans ?_))
    · gcongr
      exact le_max_left _ _
    · exact div_le_div_of_nonneg_left hnum (by positivity) (pow_le_pow_left₀ hPw.le (hu w) N)

end GlobalTheory.CompanionTheory.GaugeSpanK
