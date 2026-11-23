import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

noncomputable section

open Matrix Topology

namespace UpperTheory.V.Af.Smo

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

private theorem colM_mul_neg (m : Fin n) (u v : Fin n → R) (huv : u + v = 0) : colM m u * colM m v = 1 := by
  have h0 : (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then u i else 0) *
      (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then v i else 0) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Matrix.of_apply]
    by_cases h1 : k ≤ m
    · have : ¬ (i ≤ m ∧ k.val = m.val + 1) := fun h => by
        have := Fin.le_def.1 h1
        omega
      rw [if_neg this, zero_mul]
    · have : ¬ (k ≤ m ∧ j.val = m.val + 1) := fun h => h1 h.1
      rw [if_neg this, mul_zero]
  unfold colM
  rw [add_mul, mul_add, mul_add, h0, one_mul, one_mul, mul_one, add_zero, add_assoc, add_eq_left]
  ext i j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply]
  split_ifs
  · rw [add_comm]; exact congrFun huv i
  · simp

private def colU (m : Fin n) (u : Fin n → R) : GL (Fin n) R :=
  ⟨colM m u, colM m (-u), colM_mul_neg m _ _ (by simp), colM_mul_neg m _ _ (by simp)⟩

private def dlt (m : Fin n) (ξ : Fin n → R) : (Fin n → R) →+ R where
  toFun u := dotLe m ξ u - u m
  map_zero' := by simp [dotLe]
  map_add' u v := by
    have : dotLe m ξ (u + v) = dotLe m ξ u + dotLe m ξ v := by
      unfold dotLe
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · simp [mul_add]
      · simp
    rw [this, Pi.add_apply]; ring

private theorem dlt_apply (m : Fin n) (ξ u : Fin n → R) : dlt m ξ u = dotLe m ξ u - u m := rfl

private theorem dlt_one (m : Fin n) (u : Fin n → R) : dlt m ((1 : Matrix (Fin n) (Fin n) R) m) u = 0 := by
  rw [dlt_apply, sub_eq_zero]
  unfold dotLe
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · simp

private theorem dlt_single (m : Fin n) (ξ : Fin n → R) (j : Fin n) (hj : j ≤ m) (y : R) :
    dlt m ξ (Pi.single j y) = (ξ j - (1 : Matrix (Fin n) (Fin n) R) m j) * y := by
  rw [dlt_apply]
  unfold dotLe
  rw [Finset.sum_eq_single j]
  · by_cases h : m = j
    · subst h; simp [sub_mul]
    · simp [hj, Matrix.one_apply_ne h, Pi.single_eq_of_ne h]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

end Alg

section Top

variable {K : Type} [NormedField K] [CompleteSpace K] {n : ℕ}

private theorem img_nhds (U : OpenSubgroup (GL (Fin n) K)) :
    {M : Matrix (Fin n) (Fin n) K | ∃ s ∈ U, s.val = M} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) K) := by
  letI I := Matrix.linftyOpNormedRing (n := Fin n) (α := K)
  have hcs : @CompleteSpace (Matrix (Fin n) (Fin n) K) I.toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin n → Fin n → K))
  have h := (@Units.isOpenMap_val (Matrix (Fin n) (Fin n) K) I
    (@instHasSummableGeomSeriesOfCompleteSpace _ I hcs)) _ U.isOpen
  exact h.mem_nhds ⟨1, U.one_mem, rfl⟩

private theorem col_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∀ᶠ u in 𝓝 (0 : Fin n → K), ∃ s ∈ U, s.val = colM m u := by
  have hc : Continuous fun u : Fin n → K => colM m u := by
    unfold colM
    refine continuous_const.add (continuous_matrix fun i j => ?_)
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply i
    · exact continuous_const
  have h0 : colM m (0 : Fin n → K) = 1 := by
    ext i j; simp [colM]
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this (img_nhds U)

private theorem row_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ V ∈ 𝓝 (0 : K), ∀ ξ : Fin n → K, (∀ j, j ≤ m → ξ j - (1 : Matrix (Fin n) (Fin n) K) m j ∈ V) →
      ∃ s ∈ U, s.val = rowM m ξ := by
  have hc : Continuous fun u : Fin n → K => rowM m (u + (1 : Matrix (Fin n) (Fin n) K) m) := by
    unfold rowM
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    split_ifs
    · exact (continuous_apply j).add continuous_const
    · exact continuous_const
  have h0 : rowM m ((0 : Fin n → K) + (1 : Matrix (Fin n) (Fin n) K) m) = 1 := by
    ext i j
    simp only [rowM, Matrix.of_apply, zero_add]
    split_ifs with h
    · rw [h.1]
    · rfl
  have h1 := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at h1
  obtain ⟨ε, hε, h2⟩ := Metric.mem_nhds_iff.1 (h1 (img_nhds U))
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds _ hε, fun ξ hξ => ?_⟩
  have h3 : (fun j => if j ≤ m then ξ j - (1 : Matrix (Fin n) (Fin n) K) m j else 0) ∈
      Metric.ball (0 : Fin n → K) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    split_ifs with h
    · exact hξ j h
    · simpa using hε
  obtain ⟨s, hs, e⟩ := h2 h3
  refine ⟨s, hs, e.trans ?_⟩
  ext i j
  simp only [rowM, Matrix.of_apply, Pi.add_apply]
  by_cases h : i = m ∧ j ≤ m
  · simp [h]
  · rw [if_neg h, if_neg h]

private theorem step_gen (hA : AvgChar) (ψ : AddChar K ℂ) (hψ : ∀ᶠ x in 𝓝 (0 : K), ψ x = 1)
    (hD : ∀ V ∈ 𝓝 (0 : K), ∃ L : AddSubgroup K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, (∀ y ∈ L, ψ (x * y) = 1) → x ∈ V) (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ (c : GL (Fin n) K →₀ ℂ) (h : (Fin n → K) → ℂ),
      h ((1 : Matrix (Fin n) (Fin n) K) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → ∃ s ∈ U, s.val = rowM m ξ) ∧
      ∀ W : GL (Fin n) K → ℂ, (∀ g, ∀ u ∈ U, W (g * u) = W g) → ∀ p ξ,
        (∀ u (t : GL (Fin n) K), t.val = colM m u → W (p * t) = ψ (dotLe m ξ u) * W p) →
        comb c W p = h ξ * W p := by
  classical
  obtain ⟨V, hV, hrow⟩ := row_nhds m U
  obtain ⟨L₁, ho, hc, hL₁⟩ := hD V hV
  let L : AddSubgroup (Fin n → K) := AddSubgroup.pi Set.univ fun _ => L₁
  have hLo : IsOpen (L : Set (Fin n → K)) := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hLc : IsCompact (L : Set (Fin n → K)) := isCompact_univ_pi fun _ => hc
  let N : Set (Fin n → K) := {u | u ∈ L ∧ (∃ s ∈ U, s.val = colM m u) ∧ ψ (u m) = 1}
  have hN : N ∈ 𝓝 (0 : Fin n → K) := by
    refine Filter.inter_mem (hLo.mem_nhds L.zero_mem) (Filter.inter_mem (col_nhds m U) ?_)
    exact (continuous_apply m).continuousAt (x := (0 : Fin n → K)) hψ
  let L₀ := AddSubgroup.closure N
  have hle : L₀ ≤ L := (AddSubgroup.closure_le _).2 fun u hu => hu.1
  have hL₀ : IsOpen (L₀ : Set (Fin n → K)) :=
    L₀.isOpen_of_mem_nhds (Filter.mem_of_superset hN AddSubgroup.subset_closure)
  have hidx : L₀.relIndex L ≠ 0 := by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
    have := AddSubgroup.quotient_finite_of_isOpen (L₀.addSubgroupOf L) (hL₀.preimage continuous_subtype_val)
    exact AddSubgroup.index_ne_zero_of_finite
  obtain ⟨T, hT, hTL, hsum⟩ := hA _ L₀ L hle hidx
  have hcard : (T.card : ℂ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  refine ⟨∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m)),
    fun ξ => if ∀ u ∈ L, ψ (dlt m ξ u) = 1 then 1 else 0, ?_, fun ξ hξ => ?_, fun W hW p ξ hp => ?_⟩
  · simp [dlt_one]
  · have h1 : ∀ u ∈ L, ψ (dlt m ξ u) = 1 := by
      by_contra h
      exact hξ (if_neg h)
    refine hrow ξ fun j hj => hL₁ _ fun y hy => ?_
    rw [← dlt_single m ξ j hj]
    refine h1 _ fun k _ => ?_
    by_cases h : k = j
    · subst h; simpa using hy
    · rw [Pi.single_eq_of_ne h]; exact L₁.zero_mem
  · have e1 : comb (∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m))) W p =
        (T.card : ℂ)⁻¹ * (∑ t ∈ T, ψ (dlt m ξ t)) * W p := by
      unfold comb
      rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; ring), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finsupp.sum_single_index (by simp), hp t (colU m t) rfl, dlt_apply, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    by_cases h0 : W p = 0
    · simp [h0]
    congr 1
    dsimp only
    split_ifs with h
    · rw [Finset.sum_congr rfl fun t ht => h t (hTL t ht)]
      simp [hcard]
    · push Not at h
      have h2 : ∀ x ∈ L₀, ψ.compAddMonoidHom (dlt m ξ) x = 1 := by
        intro x hx
        induction hx using AddSubgroup.closure_induction with
        | mem u hu =>
          obtain ⟨-, ⟨s, hs, e⟩, h3⟩ := hu
          have h4 := hp u s e
          rw [hW p s hs] at h4
          have h5 : ψ (dotLe m ξ u) = 1 := mul_right_cancel₀ h0 (by rw [← h4, one_mul])
          rw [AddChar.compAddMonoidHom_apply, dlt_apply, AddChar.map_sub_eq_div, h5, h3, div_one]
        | zero => simp
        | add x y _ _ hx hy => rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
        | neg x _ hx => rw [AddChar.map_neg_eq_inv, hx, inv_one]
      have := hsum _ h2 h
      simp only [AddChar.compAddMonoidHom_apply] at this
      rw [this, mul_zero]

end Top

end UpperTheory.V.Af.Smo

theorem UpperTheory.V.Af.Smo.locStep :
    UpperTheory.V.Af.Smo.AvgChar → UpperTheory.V.Af.Smo.LocDual → UpperTheory.V.Af.Smo.LocStep := by
  intro hA hD E _ _ w ψ hψ h1 n m _ U
  exact UpperTheory.V.Af.Smo.step_gen hA ψ hψ (hD E w ψ h1) m U
