import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory
open scoped Pointwise

namespace GlobalTheory.PrinTwo.Dilation

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unit_ne_zero (r : kˣ) : valuation k (r : k) ≠ 0 := by simp

theorem isOpen_ball (c : k) (r : kˣ) : IsOpen (ball c r) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 (valuation k (r : k)) (val_unit_ne_zero r), fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy
  show valuation k (y - c) ≤ valuation k (r : k)
  have h := (valuation k).map_add (y - x) (x - c)
  rw [sub_add_sub_cancel] at h
  exact h.trans (max_le hy.le hx)

theorem isCompact_ball (c : k) (r : kˣ) : IsCompact (ball c r) := by
  have h := (IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k (r : k))).image
    (continuous_add_right c)
  convert h using 1
  rw [Set.image_add_right]
  ext z
  simp [ball, sub_eq_add_neg]

theorem mem_ball_self (c : k) (r : kˣ) : c ∈ ball c r := by
  simp [ball]

theorem ball_eq_of_mem {c z : k} {r : kˣ} (h : z ∈ ball c r) : ball z r = ball c r := by
  have h' : valuation k (c - z) ≤ valuation k (r : k) := by
    rw [Valuation.map_sub_swap]; exact h
  ext y
  constructor
  · intro hy
    have := (valuation k).map_add (y - z) (z - c)
    rw [sub_add_sub_cancel] at this
    exact this.trans (max_le hy (show valuation k (z - c) ≤ valuation k (r : k) from h))
  · intro hy
    have := (valuation k).map_add (y - c) (c - z)
    rw [sub_add_sub_cancel] at this
    exact this.trans (max_le hy h')

theorem ball_disjoint_of_ne {c c' : k} {r : kˣ} (h : ball c r ≠ ball c' r) : Disjoint (ball c r) (ball c' r) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact h ((ball_eq_of_mem hz).symm.trans (ball_eq_of_mem hz'))

theorem ball_subset_ball {c : k} {s t : kˣ} (hc : c ∈ ball (0 : k) t)
    (hst : valuation k (s : k) ≤ valuation k (t : k)) : ball c s ⊆ ball (0 : k) t := by
  intro y hy
  have hc' : valuation k (c - 0) ≤ valuation k (t : k) := hc
  have := (valuation k).map_add (y - c) (c - 0)
  rw [sub_add_sub_cancel] at this
  exact this.trans (max_le (hy.trans hst) hc')

theorem ball_eq_preimage (c : k) (r : kˣ) : ball c r = (fun z => -c + z) ⁻¹' ball (0 : k) r := by
  ext z
  simp only [ball, Set.mem_setOf_eq, Set.mem_preimage, sub_zero]
  rw [neg_add_eq_sub]

theorem exists_cover (s t : kˣ) (hst : valuation k (s : k) ≤ valuation k (t : k)) :
    ∃ Q : Finset (Set k), (∀ B ∈ Q, ∃ c ∈ ball (0 : k) t, B = ball c s) ∧
      ball (0 : k) t = ⋃ B ∈ Q, B := by
  classical
  obtain ⟨T, hT⟩ := (isCompact_ball (0 : k) t).elim_finite_subcover
    (fun i : ball (0 : k) t => ball (i : k) s) (fun i => isOpen_ball _ _)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self x s⟩)
  refine ⟨T.image (fun i : ball (0 : k) t => ball (i : k) s), ?_, ?_⟩
  · intro B hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    exact ⟨i, i.2, rfl⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, hx'⟩ := Set.mem_iUnion₂.1 (hT hx)
      exact Set.mem_iUnion₂.2 ⟨ball (i : k) s, Finset.mem_image_of_mem _ hi, hx'⟩
    · refine Set.iUnion₂_subset fun B hB => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
      exact ball_subset_ball i.2 hst

theorem pairwiseDisjoint_of_cover {s : kˣ} {Q : Finset (Set k)} (hQ : ∀ B ∈ Q, ∃ c : k, B = ball c s) :
    (↑Q : Set (Set k)).PairwiseDisjoint id := by
  intro B hB B' hB' hne
  obtain ⟨c, rfl⟩ := hQ B hB
  obtain ⟨c', rfl⟩ := hQ B' hB'
  exact ball_disjoint_of_ne hne

theorem smul_ball_zero (b t : kˣ) : b • ball (0 : k) t = ball (0 : k) (b * t) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show valuation k (((b⁻¹ : kˣ) : k) * x - 0) ≤ valuation k (t : k) ↔
    valuation k (x - 0) ≤ valuation k (((b * t : kˣ)) : k)
  rw [sub_zero, sub_zero, map_mul, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  exact inv_mul_le_iff₀ (zero_lt_iff.2 (val_unit_ne_zero b))

theorem card_mul_nabs {b t : kˣ} {Q : Finset (Set k)}
    (hQ : ∀ B ∈ Q, ∃ c ∈ ball (0 : k) t, B = ball c (b * t)) (hU : ball (0 : k) t = ⋃ B ∈ Q, B) :
    (Q.card : ℝ) * nabs k b = 1 := by
  borelize k
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨ball (0 : k) t, isCompact_ball 0 t⟩, by
    rw [show interior ((⟨ball (0 : k) t, isCompact_ball 0 t⟩ : TopologicalSpace.Compacts k).carrier) =
      ball (0 : k) t from (isOpen_ball 0 t).interior_eq]
    exact ⟨0, mem_ball_self 0 t⟩⟩
  set μ := Measure.addHaarMeasure K
  have h1 : μ (ball (0 : k) t) = 1 := Measure.addHaarMeasure_self
  have hd := distribHaarChar_mul μ b (ball (0 : k) t)
  rw [h1, mul_one, smul_ball_zero] at hd
  have hQ' : ∀ B ∈ Q, ∃ c : k, B = ball c (b * t) := fun B hB => by
    obtain ⟨c, -, h⟩ := hQ B hB; exact ⟨c, h⟩
  have hsum : μ (ball (0 : k) t) = Q.card * μ (ball (0 : k) (b * t)) := by
    rw [hU, show (⋃ B ∈ Q, B) = ⋃ B ∈ Q, id B from rfl,
      measure_biUnion_finset (pairwiseDisjoint_of_cover hQ') fun B hB => by
        obtain ⟨c, rfl⟩ := hQ' B hB; exact (isOpen_ball _ _).measurableSet]
    rw [Finset.sum_congr rfl (g := fun _ => μ (ball (0 : k) (b * t))) fun B hB => by
      obtain ⟨c, rfl⟩ := hQ' B hB
      rw [id, ball_eq_preimage c, measure_preimage_add], Finset.sum_const, nsmul_eq_mul]
  have e : ((Q.card : NNReal) * distribHaarChar k b : NNReal) = 1 := by
    apply ENNReal.coe_injective
    push_cast
    rw [hd, ← hsum, h1]
  have := congrArg (fun x : NNReal => (x : ℝ)) e
  push_cast at this
  simpa [nabs] using this

def ind (t : kˣ) : k → ℂ := (ball (0 : k) t).indicator 1

theorem indicator_sub_ind_mem (c : k) (s : kˣ) : (ball c s).indicator (1 : k → ℂ) - ind s ∈ elemSpan k :=
  Submodule.subset_span ⟨(c, 0, s), rfl⟩

theorem ind_mul_sub_mem_of_le {b : kˣ} (hb : valuation k (b : k) ≤ 1) (t : kˣ) :
    ind (b * t) - ((nabs k b : ℝ) : ℂ) • ind t ∈ elemSpan k := by
  classical
  have hst : valuation k ((b * t : kˣ) : k) ≤ valuation k (t : k) := by
    rw [Units.val_mul, map_mul]; exact mul_le_of_le_one_left' hb
  obtain ⟨Q, hQ, hU⟩ := exists_cover (b * t) t hst
  have hN := card_mul_nabs hQ hU
  have hN' : (Q.card : ℂ) * ((nabs k b : ℝ) : ℂ) = 1 := by exact_mod_cast hN
  have hQ' : ∀ B ∈ Q, ∃ c : k, B = ball c (b * t) := fun B hB => by
    obtain ⟨c, -, h⟩ := hQ B hB; exact ⟨c, h⟩
  have hsum : ind t = ∑ B ∈ Q, B.indicator (1 : k → ℂ) := by
    funext x
    rw [Finset.sum_apply, ind, hU]
    exact Finset.indicator_biUnion_apply Q id (pairwiseDisjoint_of_cover hQ') x
  have hmem : ind t - (Q.card : ℂ) • ind (b * t) ∈ elemSpan k := by
    have : ind t - (Q.card : ℂ) • ind (b * t) = ∑ B ∈ Q, (B.indicator (1 : k → ℂ) - ind (b * t)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← hsum, Nat.cast_smul_eq_nsmul]
    rw [this]
    refine Submodule.sum_mem _ fun B hB => ?_
    obtain ⟨c, rfl⟩ := hQ' B hB
    exact indicator_sub_ind_mem c _
  have : ind (b * t) - ((nabs k b : ℝ) : ℂ) • ind t =
      (-((nabs k b : ℝ) : ℂ)) • (ind t - (Q.card : ℂ) • ind (b * t)) := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(ind (b * t) x)) * hN'
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem nabs_inv (b : kˣ) : nabs k b⁻¹ = (nabs k b)⁻¹ := by
  simp [nabs, map_inv]

theorem ind_mul_sub_mem (b t : kˣ) : ind (b * t) - ((nabs k b : ℝ) : ℂ) • ind t ∈ elemSpan k := by
  rcases le_total (valuation k (b : k)) 1 with hb | hb
  · exact ind_mul_sub_mem_of_le hb t
  · have hb' : valuation k ((b⁻¹ : kˣ) : k) ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]; exact inv_le_one_of_one_le₀ hb
    have h := ind_mul_sub_mem_of_le hb' (b * t)
    rw [inv_mul_cancel_left] at h
    have hne : ((nabs k b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nabs_pos' k b).ne'
    have : ind (b * t) - ((nabs k b : ℝ) : ℂ) • ind t =
        (-((nabs k b : ℝ) : ℂ)) • (ind t - ((nabs k b⁻¹ : ℝ) : ℂ) • ind (b * t)) := by
      rw [nabs_inv]
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h

theorem indicator_ball_mul (a : kˣ) (c : k) (r : kˣ) (x : k) :
    (ball c r).indicator (1 : k → ℂ) ((a : k) * x) =
      (ball (((a⁻¹ : kˣ) : k) * c) (a⁻¹ * r)).indicator 1 x := by
  have e : (a : k) * x - c = (a : k) * (x - ((a⁻¹ : kˣ) : k) * c) := by
    rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul]
  have hmem : (a : k) * x ∈ ball c r ↔ x ∈ ball (((a⁻¹ : kˣ) : k) * c) (a⁻¹ * r) := by
    show valuation k ((a : k) * x - c) ≤ valuation k (r : k) ↔
      valuation k (x - ((a⁻¹ : kˣ) : k) * c) ≤ valuation k (((a⁻¹ * r : kˣ)) : k)
    rw [e, map_mul, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      le_inv_mul_iff₀ (zero_lt_iff.2 (val_unit_ne_zero a))]
  by_cases h : x ∈ ball (((a⁻¹ : kˣ) : k) * c) (a⁻¹ * r)
  · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem h]; rfl
  · rw [Set.indicator_of_notMem (mt hmem.1 h), Set.indicator_of_notMem h]

end GlobalTheory.PrinTwo.Dilation

namespace GlobalTheory.PrinTwo

open Dilation

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dilate_sub_mem_elemSpan (Φ : k → ℂ) (hΦ : IsLC Φ) (hΦ' : IsCS Φ) (a : kˣ) :
    (fun x => Φ (a * x) - ((absPow k 1 a : ℂˣ) : ℂ)⁻¹ * Φ x) ∈ elemSpan k := by
  classical
  obtain ⟨r, hr⟩ := hΦ
  obtain ⟨R, hR⟩ := hΦ'
  let s : kˣ := if valuation k (r : k) ≤ valuation k (R : k) then r else R
  have hsr : valuation k (s : k) ≤ valuation k (r : k) := by
    by_cases h : valuation k (r : k) ≤ valuation k (R : k)
    · simp only [s, if_pos h, le_refl]
    · simp only [s, if_neg h]; exact (not_le.1 h).le
  have hsR : valuation k (s : k) ≤ valuation k (R : k) := by
    by_cases h : valuation k (r : k) ≤ valuation k (R : k)
    · simp only [s, if_pos h]; exact h
    · simp only [s, if_neg h, le_refl]
  obtain ⟨Q, hQ, hU⟩ := exists_cover s R hsR
  have hQ' : ∀ B ∈ Q, ∃ c : k, B = ball c s := fun B hB => by
    obtain ⟨c, -, h⟩ := hQ B hB; exact ⟨c, h⟩
  set α : ℂ := ((nabs k a⁻¹ : ℝ) : ℂ) with hαdef
  have hα : ((absPow k 1 a : ℂˣ) : ℂ)⁻¹ = α := by
    rw [val_absPow, Complex.cpow_one, hαdef, nabs_inv]; push_cast; rfl
  have hdec : Φ = ∑ B ∈ Q, B.indicator Φ := by
    funext x
    rw [Finset.sum_apply]
    refine Eq.trans ?_ (Finset.indicator_biUnion_apply Q id (pairwiseDisjoint_of_cover hQ') x)
    show Φ x = (⋃ B ∈ Q, B).indicator Φ x
    rw [← hU]
    by_cases hx : x ∈ ball (0 : k) R
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      apply hR
      have : ¬ valuation k (x - 0) ≤ valuation k (R : k) := hx
      rw [sub_zero] at this
      exact not_le.1 this
  let D : (k → ℂ) →ₗ[ℂ] (k → ℂ) := LinearMap.funLeft ℂ ℂ (fun x => (a : k) * x) - α • LinearMap.id
  have hD : ∀ f x, D f x = f ((a : k) * x) - α * f x := fun f x => rfl
  have hΨ : (fun x => Φ (a * x) - ((absPow k 1 a : ℂˣ) : ℂ)⁻¹ * Φ x) = D Φ := by
    funext x; rw [hD, hα]
  rw [hΨ, hdec, map_sum]
  refine Submodule.sum_mem _ fun B hB => ?_
  obtain ⟨c, rfl⟩ := hQ' B hB
  have hB : (ball c s).indicator Φ = Φ c • (ball c s).indicator (1 : k → ℂ) := by
    funext x
    by_cases hx : x ∈ ball c s
    · rw [Set.indicator_of_mem hx, Pi.smul_apply, Set.indicator_of_mem hx, Pi.one_apply, smul_eq_mul,
        mul_one]
      have := hr c (x - c) (le_trans hx hsr)
      rwa [add_sub_cancel] at this
    · rw [Set.indicator_of_notMem hx, Pi.smul_apply, Set.indicator_of_notMem hx, smul_zero]
  rw [hB, map_smul]
  refine Submodule.smul_mem _ _ ?_
  have hsplit : D ((ball c s).indicator 1) =
      ((ball (((a⁻¹ : kˣ) : k) * c) (a⁻¹ * s)).indicator (1 : k → ℂ) - ind (a⁻¹ * s)) +
        (ind (a⁻¹ * s) - α • ind s) - α • ((ball c s).indicator (1 : k → ℂ) - ind s) := by
    funext x
    rw [hD, indicator_ball_mul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (indicator_sub_ind_mem _ _) (ind_mul_sub_mem _ _))
    (Submodule.smul_mem _ _ (indicator_sub_ind_mem _ _))

end GlobalTheory.PrinTwo

theorem GlobalTheory.PrinTwo.dilate_sub_mem_elemSpan_target : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Φ : k → ℂ), GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ → ∀ a : kˣ, (fun x => Φ (a * x) - ((GlobalTheory.SmGL.absPow k 1 a : ℂˣ) : ℂ)⁻¹ * Φ x) ∈ GlobalTheory.PrinTwo.elemSpan k :=
  fun _ _ _ _ _ Φ hΦ hΦ' a => GlobalTheory.PrinTwo.dilate_sub_mem_elemSpan Φ hΦ hΦ' a
