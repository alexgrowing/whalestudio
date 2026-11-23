import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open Filter Topology
open scoped SchwartzMap Pointwise

namespace GlobalTheory
namespace FrechetOpenMapping

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]

theorem tendsto_inv_nat_complex : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)

theorem closure_image_mem_nhds [BaireSpace F] (T : E →L[ℂ] F) (hT : Function.Surjective T)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) : closure (T '' U) ∈ 𝓝 (0 : F) := by
  obtain ⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (0 : E), ∀ a ∈ W, ∀ b ∈ W, a - b ∈ U := by
    have : Tendsto (fun p : E × E => p.1 - p.2) (𝓝 (0, 0)) (𝓝 0) := by
      exact (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 (this hU)
    exact ⟨A ∩ B, inter_mem hA hB, fun a ha b hb => hAB (Set.mk_mem_prod ha.1 hb.2)⟩
  set A := closure (T '' W) with hAdef
  have hcov : ⋃ n : ℕ, ((n + 1 : ℕ) : ℂ) • A = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hT y
    have ht : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹ • x) atTop (𝓝 0) := by
      simpa using tendsto_inv_nat_complex.smul_const x
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ht hW)
    have hmem := hN (N + 1) (Nat.le_succ N)
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    have hne : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    refine ⟨T (((N + 1 : ℕ) : ℂ)⁻¹ • x), subset_closure ⟨_, hmem, rfl⟩, ?_⟩
    simp only [map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hcl : ∀ n : ℕ, IsClosed (((n + 1 : ℕ) : ℂ) • A) := fun n =>
    isClosed_closure.smul_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  haveI : Nonempty F := ⟨0⟩
  obtain ⟨n, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [interior_smul₀ hne] at hy
  obtain ⟨y, hy, -⟩ := hy
  have hnb : {z : F | y + z ∈ interior A} ∈ 𝓝 (0 : F) := by
    have hc : Continuous fun z : F => y + z := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hy)
  refine mem_of_superset hnb fun z hz => ?_
  have h1 : y + z ∈ closure (T '' W) := interior_subset hz
  have h2 : y ∈ closure (T '' W) := interior_subset hy
  have := map_mem_closure₂ (f := fun a b : F => a - b) (u := T '' U)
    (continuous_fst.sub continuous_snd) h1 h2 (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a - b, hWU a ha b hb, map_sub T a b⟩)
  simpa using this

theorem sum_Ico_mem {U : ℕ → Set E} (h0 : ∀ k, (0 : E) ∈ U k)
    (hadd : ∀ k, ∀ a ∈ U (k + 1), ∀ b ∈ U (k + 1), a + b ∈ U k) {x : ℕ → E}
    (hx : ∀ j, x j ∈ U (j + 1)) : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U m := by
  intro n
  induction n with
  | zero => intro m; simpa using h0 m
  | succ n ih =>
    intro m
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show m + (n + 1) = m + 1 + n by omega]
    exact hadd m _ (hx m) _ (ih (m + 1))

theorem exists_halving [(𝓝 (0 : E)).IsCountablyGenerated] {U₀ : Set E} (h : U₀ ∈ 𝓝 (0 : E)) :
    ∃ U : ℕ → Set E, U 0 = U₀ ∧ (∀ k, U k ∈ 𝓝 (0 : E)) ∧
      (∀ k, ∀ a ∈ U (k + 1), ∀ b ∈ U (k + 1), a + b ∈ U k) ∧
      (∀ k, ∀ a ∈ U (k + 1), -a ∈ U (k + 1)) ∧ ∀ N ∈ 𝓝 (0 : E), ∃ k, U k ⊆ N := by
  classical
  obtain ⟨B, hB⟩ := (𝓝 (0 : E)).exists_antitone_basis
  let half : Set E → Set E := fun S =>
    if hS : S ∈ 𝓝 (0 : E) then Classical.choose (exists_nhds_zero_half hS) ∩
      -Classical.choose (exists_nhds_zero_half hS) else Set.univ
  have hhalf : ∀ S ∈ 𝓝 (0 : E), half S ∈ 𝓝 (0 : E) ∧ (∀ v ∈ half S, ∀ w ∈ half S, v + w ∈ S) ∧
      ∀ v ∈ half S, -v ∈ half S := by
    intro S hS
    obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_nhds_zero_half hS)
    simp only [half, dif_pos hS]
    refine ⟨inter_mem h1 (neg_mem_nhds_zero E h1), fun v hv w hw => h2 v hv.1 w hw.1, ?_⟩
    rintro v ⟨hv1, hv2⟩
    exact ⟨hv2, by simpa using hv1⟩
  let U : ℕ → Set E := fun n => Nat.rec U₀ (fun k Uk => half Uk ∩ (B k ∩ -B k)) n
  have hU : ∀ k, U k ∈ 𝓝 (0 : E) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih => exact inter_mem (hhalf _ ih).1 (inter_mem (hB.mem k) (neg_mem_nhds_zero E (hB.mem k)))
  refine ⟨U, rfl, hU, fun k a ha b hb => (hhalf _ (hU k)).2.1 a ha.1 b hb.1, ?_, fun N hN => ?_⟩
  · rintro k a ⟨ha1, ha2, ha3⟩
    exact ⟨(hhalf _ (hU k)).2.2 a ha1, by simpa using ha3, by simpa using ha2⟩
  · obtain ⟨k, -, hk⟩ := hB.toHasBasis.mem_iff.1 hN
    exact ⟨k + 1, fun a ha => hk ha.2.1⟩

theorem image_mem_nhds [CompleteSpace E] [(𝓝 (0 : E)).IsCountablyGenerated] [T2Space F] [BaireSpace F]
    (T : E →L[ℂ] F) (hT : Function.Surjective T) {U₀ : Set E} (h : U₀ ∈ 𝓝 (0 : E)) :
    T '' U₀ ∈ 𝓝 (0 : F) := by
  classical
  obtain ⟨U, rfl, hU, hadd, hneg, hbas⟩ := exists_halving h
  have h0 : ∀ k, (0 : E) ∈ U k := fun k => mem_of_mem_nhds (hU k)
  have hanti : ∀ k, U (k + 1) ⊆ U k := fun k a ha => by simpa using hadd k a ha 0 (h0 _)
  have hmono : ∀ k l, k ≤ l → U l ⊆ U k := by
    intro k l hkl
    induction hkl with
    | refl => exact le_rfl
    | step _ ih => exact (hanti _).trans ih
  let V : ℕ → Set F := fun k => closure (T '' U k)
  have hVn : ∀ k, V k ∈ 𝓝 (0 : F) := fun k => closure_image_mem_nhds T hT (hU k)
  have pick : ∀ k, ∀ r ∈ V k, ∃ x ∈ U k, r - T x ∈ V (k + 1) := by
    intro k r hr
    have hnb : {w : F | r - w ∈ V (k + 1)} ∈ 𝓝 r := by
      have hc : Continuous fun w : F => r - w := continuous_const.sub continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hVn (k + 1))
    obtain ⟨_, hw, ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hr _ hnb
    exact ⟨x, hx, hw⟩
  refine mem_of_superset (hVn 2) fun y hy => ?_
  let step : ℕ → F → E := fun k r => if hr : r ∈ V k then Classical.choose (pick k r hr) else 0
  have hstep : ∀ k r, r ∈ V k → step k r ∈ U k ∧ r - T (step k r) ∈ V (k + 1) := by
    intro k r hr
    simp only [step, dif_pos hr]
    exact Classical.choose_spec (pick k r hr)
  let r : ℕ → F := fun n => Nat.rec y (fun n rn => rn - T (step (n + 2) rn)) n
  have hr : ∀ n, r n ∈ V (n + 2) := by
    intro n
    induction n with
    | zero => exact hy
    | succ n ih => exact (hstep _ _ ih).2
  let x : ℕ → E := fun n => step (n + 2) (r n)
  have hx : ∀ n, x n ∈ U (n + 2) := fun n => (hstep _ _ (hr n)).1
  let s : ℕ → E := fun n => ∑ j ∈ Finset.range n, x j
  have hrs : ∀ n, r n = y - T (s n) := by
    intro n
    induction n with
    | zero => simp [r, s]
    | succ n ih =>
      show r n - T (x n) = _
      rw [ih]
      simp only [s, Finset.sum_range_succ, map_add]
      abel
  have htail : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U (m + 1) :=
    sum_Ico_mem (U := fun k => U (k + 1)) (fun k => h0 _) (fun k => hadd (k + 1)) hx
  have hdiff : ∀ m n, m ≤ n → s n - s m ∈ U (m + 1) := by
    intro m n hmn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := htail d m
    rwa [Finset.sum_Ico_eq_sub _ hmn] at this
  have hs1 : ∀ n, s n ∈ U 1 := fun n => by simpa [s] using hdiff 0 n (Nat.zero_le n)
  have hcau : CauchySeq s := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
    intro N hN
    obtain ⟨k, hk⟩ := hbas N hN
    refine mem_map.2 (mem_atTop_sets.2 ⟨(k, k), fun p hp => hk ?_⟩)
    obtain ⟨hp1, hp2⟩ := hp
    show s p.2 - s p.1 ∈ U k
    rcases le_total p.1 p.2 with hle | hle
    · exact hmono k (p.1 + 1) (by simp at hp1; omega) (hdiff _ _ hle)
    · have := hneg p.2 _ (hdiff _ _ hle)
      rw [neg_sub] at this
      exact hmono k (p.2 + 1) (by simp at hp2; omega) this
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  have hzU : z ∈ closure (U 1) := mem_closure_of_tendsto hz (Eventually.of_forall hs1)
  have hz0 : z ∈ U 0 := by
    have hnb : {q : E | z - q ∈ U 1} ∈ 𝓝 z :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU 1)
    obtain ⟨q, hq, hq1⟩ := mem_closure_iff_nhds.1 hzU _ hnb
    simpa using hadd 0 _ hq _ hq1
  refine ⟨z, hz0, ?_⟩
  have h1 : Tendsto (fun n => T (s n)) atTop (𝓝 (T z)) := (T.continuous.tendsto z).comp hz
  have h2 : Tendsto r atTop (𝓝 0) := by
    intro N hN
    obtain ⟨N', ⟨hN', hN'c⟩, hN'N⟩ := (closed_nhds_basis (0 : F)).mem_iff.1 hN
    have hpre : T ⁻¹' N' ∈ 𝓝 (0 : E) :=
      T.continuous.continuousAt.preimage_mem_nhds (by simpa using hN')
    obtain ⟨k, hk⟩ := hbas _ hpre
    refine mem_map.2 (mem_atTop_sets.2 ⟨k, fun n hn => hN'N ?_⟩)
    have hsub : V (n + 2) ⊆ N' := closure_minimal (by
      rintro _ ⟨a, ha, rfl⟩
      exact hk (hmono k (n + 2) (by omega) ha)) hN'c
    exact hsub (hr n)
  have h3 : Tendsto (fun n => T (s n)) atTop (𝓝 y) := by
    have := (tendsto_const_nhds (x := y)).sub h2
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [hrs n]
    abel
  exact tendsto_nhds_unique h1 h3

theorem exists_inverse [CompleteSpace E] [(𝓝 (0 : E)).IsCountablyGenerated] [T2Space F]
    [BaireSpace F] (T : E →L[ℂ] F) (hT : Function.Bijective T) :
    ∃ S : F →L[ℂ] E, ∀ f, T (S f) = f := by
  let e := LinearEquiv.ofBijective (T : E →ₗ[ℂ] F) hT
  have hc : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro U hU
    rw [mem_map]
    refine mem_of_superset (image_mem_nhds T hT.2 hU) ?_
    rintro _ ⟨x, hx, rfl⟩
    show e.symm (e x) ∈ U
    rw [e.symm_apply_apply]
    exact hx
  exact ⟨⟨e.symm.toLinearMap, hc⟩, fun f => e.apply_symm_apply f⟩

theorem baireSpace_of_complete (X : Type*) [UniformSpace X] [AddGroup X] [IsUniformAddGroup X]
    [(𝓝 (0 : X)).IsCountablyGenerated] [CompleteSpace X] : BaireSpace X := by
  haveI := IsUniformAddGroup.uniformity_countably_generated (α := X)
  letI := UniformSpace.pseudoMetricSpace X
  infer_instance

theorem schwartz_exists_inverse : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    Function.Bijective T → ∃ S : SchwartzMap W ℂ →L[ℂ] SchwartzMap V ℂ, ∀ f, T (S f) = f := by
  intro V W _ _ _ _ T hT
  haveI : BaireSpace (SchwartzMap W ℂ) := baireSpace_of_complete _
  exact exists_inverse T hT

end FrechetOpenMapping
end GlobalTheory
