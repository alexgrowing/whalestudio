import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DoubleCosetSetoidRelIffMem
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.SmoothUnitary

open GlobalTheory.PRep

section

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def stab (π : G →* (H →L[ℂ] H)) (v : H) : Subgroup G := GlobalTheory.DoubleCosetSetoid.clmStabilizer π v

theorem inner_map_map_of_norm {π : G →* (H →L[ℂ] H)} (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (x y : H) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(π g : H →ₗ[ℂ] H), hπ g⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem exists_mean (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (K : Subgroup G) (w : H)
    (hf : (Set.range fun k : K => π (k : G) w).Finite) :
    ∃ m ∈ Submodule.span ℂ (Set.range fun k : K => π (k : G) w), (∀ k ∈ K, π k m = m) ∧
      ∀ u : H, (∀ k ∈ K, π k u = u) → ⟪u, m⟫_ℂ = ⟪u, w⟫_ℂ := by
  classical
  set O := hf.toFinset with hO
  have hmem : ∀ z, z ∈ O ↔ ∃ k : K, π (k : G) w = z := fun z => by simp [O]
  have hw : w ∈ O := (hmem w).2 ⟨1, by simp⟩
  have hc : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hw⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ z ∈ O, z, ?_, fun k hk => ?_, fun u hu => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.subset_span ?_)
    obtain ⟨k, rfl⟩ := (hmem z).1 hz
    exact ⟨k, rfl⟩
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (fun z => π k z) (fun z => π k⁻¹ z) (fun z hz => ?_) (fun z hz => ?_)
      (fun z _ => ?_) (fun z _ => ?_) (fun z _ => rfl)
    · obtain ⟨k', rfl⟩ := (hmem z).1 hz
      exact (hmem _).2 ⟨⟨k, hk⟩ * k', by simp⟩
    · obtain ⟨k', rfl⟩ := (hmem z).1 hz
      exact (hmem _).2 ⟨⟨k, hk⟩⁻¹ * k', by simp⟩
    · simp [← ContinuousLinearMap.mul_apply, ← map_mul]
    · simp [← ContinuousLinearMap.mul_apply, ← map_mul]
  · have h1 : ∀ z ∈ O, ⟪u, z⟫_ℂ = ⟪u, w⟫_ℂ := fun z hz => by
      obtain ⟨k, rfl⟩ := (hmem z).1 hz
      rw [← inner_map_map_of_norm hπ k u w, hu k k.2]
    rw [inner_smul_right, inner_sum, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_compactOpen_subset [NonarchimedeanGroup G] [LocallyCompactSpace G] {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨C, hC, hCU, hCc⟩ := local_compact_nhds hU
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean C hC
  exact ⟨V.toSubgroup, V.isOpen, hCc.of_isClosed_subset V.isClosed hV, hV.trans hCU⟩

theorem finite_orbit (π : G →* (H →L[ℂ] H)) {K : Subgroup G} (hK : IsCompact (K : Set G)) {w : H}
    (hw : IsOpen (stab π w : Set G)) : (Set.range fun k : K => π (k : G) w).Finite := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen ((stab π w).subgroupOf K) (hw.preimage continuous_subtype_val)
  refine (Set.finite_range (fun q : K ⧸ (stab π w).subgroupOf K => π ((q.out : K) : G) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨QuotientGroup.mk k, ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul ((stab π w).subgroupOf K) k
  have h2 : π ((s : K) : G) w = w := Subgroup.mem_subgroupOf.1 s.2
  simp only [hs, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply, h2]

end

theorem exists_fixed_ne_zero : ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (K : Subgroup G) (x : H), x ≠ 0 →
      (∀ k ∈ K, ‖π k x - x‖ ≤ ‖x‖ / 2) → ∃ y : H, y ≠ 0 ∧ ∀ k ∈ K, π k y = y := by
  intro G _ H _ _ _ π hπ K x hx hK
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set O : Set H := Set.range fun k : K => π (k : G) x
  set C : Set H := closure (convexHull ℝ O)
  have hconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hxC : x ∈ C := subset_closure (subset_convexHull ℝ O ⟨1, by simp⟩)
  have hball : C ⊆ Metric.closedBall x (‖x‖ / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hK k k.2
  have hinv : ∀ k ∈ K, ∀ z ∈ C, π k z ∈ C := by
    intro k hk z hz
    let T : H →L[ℝ] H := (π k).restrictScalars ℝ
    have hO : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨k', rfl⟩, rfl⟩
      exact ⟨⟨k, hk⟩ * k', by simp [T]⟩
    have h1 : T '' convexHull ℝ O ⊆ convexHull ℝ O := by
      have e := (T : H →ₗ[ℝ] H).image_convexHull O
      change (T : H →ₗ[ℝ] H) '' convexHull ℝ O ⊆ _
      rw [e]
      exact convexHull_min ((show (T : H →ₗ[ℝ] H) '' O ⊆ O from hO).trans (subset_convexHull ℝ O)) (convex_convexHull ℝ O)
    have h2 : T '' C ⊆ C := (image_closure_subset_closure_image T.continuous).trans (closure_mono h1)
    exact h2 ⟨z, hz, rfl⟩
  obtain ⟨y, hyC, hy⟩ := exists_norm_eq_iInf_of_complete_convex ⟨x, hxC⟩ isClosed_closure.isComplete hconv 0
  have hmin : ∀ z ∈ C, ‖y‖ ≤ ‖z‖ := fun z hz => by
    have := ciInf_le (f := fun w : C => ‖(0 : H) - (w : H)‖) ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨z, hz⟩ : C)
    simp only [zero_sub, norm_neg] at hy this
    rw [← hy] at this
    exact this
  refine ⟨y, fun h0 => ?_, fun k hk => ?_⟩
  · have h1 := hball (h0 ▸ hyC)
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at h1
    have := norm_pos_iff.2 hx
    linarith
  · set z := π k y
    have hz : z ∈ C := hinv k hk y hyC
    have hzn : ‖z‖ = ‖y‖ := hπ k y
    have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z ∈ C := hconv hyC hz (by norm_num) (by norm_num) (by norm_num)
    have h3 := hmin _ hmid
    have h4 : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z = (1 / 2 : ℝ) • (y + z) := by rw [smul_add]
    rw [h4, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h3
    have hp := parallelogram_law_with_norm ℂ y z
    rw [hzn] at hp
    have h5 : ‖y - z‖ * ‖y - z‖ ≤ 0 := by nlinarith [norm_nonneg (y + z), norm_nonneg y]
    have h6 : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h6)).symm

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult in

theorem isIrreducible_isAdmissible_smRep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsIrrUnitary π →
    (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) →
      (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  intro G _ _ _ _ _ H _ _ π hπ hfin
  have hc := hπ.complete
  have hu := hπ.unitary
  have memF : ∀ (K : Subgroup G) (u : H), u ∈ fixed (toRep π) K ↔ ∀ k ∈ K, π k u = u := fun K u => by
    change (∀ k : K, toRep π k u = ((1 : K →* ℂˣ) k : ℂ) • u) ↔ _
    simp
  have memV : ∀ v : H, v ∈ smoothPart (toRep π) ↔ IsOpen (stab π v : Set G) := fun v => Iff.rfl
  refine ⟨?_, isSmooth_smoothRep (toRep π), fun K hKo hKc => ?_⟩
  swap
  · haveI := hfin K hKo hKc
    let f : fixed (smRep π) K →ₗ[ℂ] fixed (toRep π) K :=
      { toFun := fun v => ⟨(v : smoothPart (toRep π)).1, (memF K _).2 fun k hk => by
            have h : smRep π k (v : smoothPart (toRep π)) = v := by simpa using v.2 ⟨k, hk⟩
            exact congrArg Subtype.val h⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_injective f fun a b e => by
      have := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext this)
  have hex : ∃ y : H, y ≠ 0 ∧ y ∈ smoothPart (toRep π) := by
    have := hπ.irred.1
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hx2 : 0 < ‖x‖ / 2 := by have := norm_pos_iff.2 hx; positivity
    have hU : {g : G | ‖π g x - x‖ < ‖x‖ / 2} ∈ nhds (1 : G) := by
      have hcont : Continuous fun g => ‖π g x - x‖ := ((hu.continuous_apply x).sub continuous_const).norm
      exact (isOpen_lt hcont continuous_const).mem_nhds (by simpa using hx2)
    obtain ⟨K, hKo, -, hKU⟩ := exists_compactOpen_subset hU
    obtain ⟨y, hy, hyK⟩ := exists_fixed_ne_zero G H π hu.norm_apply K x hx (fun k hk => (hKU hk).le)
    exact ⟨y, hy, (memV y).2 (Subgroup.isOpen_mono (H₁ := K) (fun k hk => hyK k hk) hKo)⟩
  obtain ⟨y, hy0, hy⟩ := hex
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hy0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1
    (show (⟨y, hy⟩ : smoothPart (toRep π)) ∈ (⊥ : Subrepresentation (smRep π)).toSubmodule from
      e ▸ Submodule.mem_top)))⟩, eq_bot_or_eq_top := fun S => ?_ }
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let V := smoothPart (toRep π)
  let W' : Submodule ℂ H := S.toSubmodule.map V.subtype
  have hWst : ∀ g, ∀ w ∈ W', π g w ∈ W' := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨smRep π g w, S.apply_mem_toSubmodule g hw, rfl⟩
  have hWV : ∀ w ∈ W', w ∈ V := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hcl : W'.topologicalClosure = ⊤ := by
    refine (hπ.irred.2 _ ⟨W'.isClosed_topologicalClosure, fun g v hv => ?_⟩).resolve_left ?_
    · exact Submodule.topologicalClosure_minimal W' (t := W'.topologicalClosure.comap (π g : H →ₗ[ℂ] H))
        (fun w hw => W'.le_topologicalClosure (hWst g w hw))
        (W'.isClosed_topologicalClosure.preimage (π g).continuous) hv
    · intro e
      have hS' : S.toSubmodule ≠ ⊥ := fun e' => hS (Subrepresentation.ext e')
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hS'
      have h1 : (w : H) ∈ W'.topologicalClosure := W'.le_topologicalClosure ⟨w, hw, rfl⟩
      rw [e, Submodule.mem_bot] at h1
      exact hw0 (Subtype.ext h1)
  have key : ∀ v ∈ V, v ∈ W' := by
    intro v hv
    obtain ⟨K, hKo, hKc, hKv⟩ := exists_compactOpen_subset (((memV v).1 hv).mem_nhds (one_mem (stab π v)))
    haveI := hfin K hKo hKc
    let M : Submodule ℂ H := W' ⊓ fixed (toRep π) K
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
    have hvF : v ∈ fixed (toRep π) K := (memF K v).2 fun k hk => hKv hk
    have huF : v - M.starProjection v ∈ fixed (toRep π) K :=
      Submodule.sub_mem _ hvF (Submodule.mem_inf.1 (M.starProjection_apply_mem v)).2
    have huM := M.sub_starProjection_mem_orthogonal v
    have horth : ∀ w ∈ W', ⟪v - M.starProjection v, w⟫_ℂ = 0 := by
      intro w hw
      obtain ⟨m, hm, hmK, hmu⟩ := exists_mean π hu.norm_apply K w (finite_orbit π hKc ((memV w).1 (hWV w hw)))
      have hmW : m ∈ W' := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hWst k w hw) hm
      rw [← hmu _ ((memF K _).1 huF)]
      exact (Submodule.mem_orthogonal' _ _).1 huM m ⟨hmW, (memF K m).2 hmK⟩
    have hu0 : v - M.starProjection v = 0 := by
      have hle : W'.topologicalClosure ≤ LinearMap.ker (innerₛₗ ℂ (v - M.starProjection v)) :=
        Submodule.topologicalClosure_minimal _ (fun w hw => horth w hw)
          (ContinuousLinearMap.isClosed_ker (innerSL ℂ (v - M.starProjection v)))
      have h1 := hle (hcl ▸ Submodule.mem_top : v - M.starProjection v ∈ W'.topologicalClosure)
      exact inner_self_eq_zero.1 h1
    have hvM : v ∈ M := (sub_eq_zero.1 hu0).symm ▸ M.starProjection_apply_mem v
    exact hvM.1
  refine Subrepresentation.ext (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨w, hw, e⟩ := key v.1 v.2
  exact (Subtype.ext e : w = v) ▸ hw

end GlobalTheory.SmoothUnitary
