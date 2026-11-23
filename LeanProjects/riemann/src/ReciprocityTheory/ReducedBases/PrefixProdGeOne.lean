import ReciprocityTheory.ReducedBases.TBInjective

noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace Matrix

variable {d : ℕ}

lemma prefix_prod_ge_one (e : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (hU : LinearIndependent ℝ (fun i => fB 1 (e i))) (k : Fin d) :
    1 ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 := by
  classical
  set v : Fin d → EuclideanSpace ℝ (Fin d) := fun i => fB 1 (e i) with hv_def
  have hk : k.val + 1 ≤ d := k.isLt
  obtain ⟨w, hw_def⟩ : ∃ w : Fin (k.val + 1) → EuclideanSpace ℝ (Fin d),
      w = fun i => v (Fin.castLE hk i) := ⟨_, rfl⟩
  have hwi : ∀ i, w i = v (Fin.castLE hk i) := fun i => by rw [hw_def]
  have hw : LinearIndependent ℝ w := by
    rw [hw_def]; exact hU.comp _ (Fin.castLE_injective hk)
  have hgs : ∀ i, gs w i = gs v (Fin.castLE hk i) := by
    intro i
    apply gs_eq_of w i (gs v (Fin.castLE hk i))
    · rw [hwi i]
      refine Submodule.span_mono ?_ (b_sub_gs_mem v (Fin.castLE hk i))
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j.val < i.val := Set.mem_Iio.mp hj
      refine ⟨⟨j.val, by omega⟩, Fin.lt_iff_val_lt_val.mpr hj', ?_⟩
      rw [hwi]
      exact congrArg v (Fin.ext rfl)
    · intro j hj
      rw [hwi j]
      exact gs_inner_b_of_lt v (show Fin.castLE hk j < Fin.castLE hk i from hj)
  have hprod : ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs v j‖ ^ 2 =
      ∏ i, ‖gs w i‖ ^ 2 := by
    symm
    refine Finset.prod_bij (fun i _ => Fin.castLE hk i) ?_ ?_ ?_ ?_
    · intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.le_iff_val_le_val, Fin.coe_castLE]
      have := i.isLt
      omega
    · intro a _ b _ h
      exact Fin.castLE_injective hk h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hj' : j.val ≤ k.val := Fin.le_iff_val_le_val.mp hj
      exact ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro i _
      rw [hgs i]
  have hdet := det_gram_eq w hw
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) ℤ,
      Matrix.gram ℝ w = G.map (Int.cast) := by
    refine ⟨Matrix.of fun a b => ∑ l, e (Fin.castLE hk a) l * e (Fin.castLE hk b) l, ?_⟩
    ext a b
    rw [Matrix.gram_apply, Matrix.map_apply, Matrix.of_apply, hwi, hwi]
    simp [hv_def, fB_apply, toReal, PiLp.inner_apply, Matrix.one_mulVec, mul_comm]
  have hdetZ : (Matrix.gram ℝ w).det = ((G.det : ℤ) : ℝ) := by
    rw [hG]
    have := (Int.castRingHom ℝ).map_det G
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hpos : 0 < ∏ i, ‖gs w i‖ ^ 2 := by
    apply Finset.prod_pos
    intro i _
    exact pow_pos (norm_pos_iff.mpr (gs_ne_zero w hw i)) 2
  have h0 : (0 : ℝ) < (G.det : ℝ) := by rw [← hdetZ, hdet]; exact hpos
  have h1 : (0 : ℤ) < G.det := by exact_mod_cast h0
  have h2 : (1 : ℤ) ≤ G.det := by omega
  rw [hprod, ← hdet, hdetZ]
  exact_mod_cast h2

lemma hlow_of (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B) :
    ∃ c : ℝ, 0 < c ∧ ∀ (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (k : Fin d),
      c ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by
  classical
  obtain ⟨K, hKpos, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (TB B)).mp (TB_injective A B hA hAB)
  have hbound : ∀ v, ‖v‖ ≤ (K : ℝ) * ‖TB B v‖ := by
    intro v
    have h := hK.le_mul_dist v 0
    simpa [dist_zero_right] using h
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  set m : ℝ := min 1 (((K : ℝ)⁻¹) ^ 2) with hm
  have hm0 : 0 < m := lt_min one_pos (pow_pos (inv_pos.mpr hK0) 2)
  have hm1 : m ≤ 1 := min_le_left _ _
  refine ⟨m ^ d, pow_pos hm0 d, ?_⟩
  intro e k
  obtain ⟨h1, -⟩ := li_basis A B hA hAB e
  have hone := prefix_prod_ge_one e h1 k
  have hterm : ∀ j : Fin d, m * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 ≤
      ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by
    intro j
    have h := gs_TB B hbound (fun i => fB 1 (e i)) j
    have hw : (fun i => TB B (fB 1 (e i))) = (fun i => fB B (e i)) := by
      funext i; exact (fB_eq_TB B (e i)).symm
    rw [hw] at h
    have h3 : (K : ℝ)⁻¹ * ‖gs (fun i => fB 1 (e i)) j‖ ≤ ‖gs (fun i => fB B (e i)) j‖ := by
      rw [inv_mul_le_iff₀ hK0]; exact h
    have h4 : 0 ≤ (K : ℝ)⁻¹ * ‖gs (fun i => fB 1 (e i)) j‖ := by positivity
    calc m * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2
        ≤ ((K : ℝ)⁻¹) ^ 2 * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = ((K : ℝ)⁻¹ * ‖gs (fun i => fB 1 (e i)) j‖) ^ 2 := by ring
      _ ≤ ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by gcongr
  set S := univ.filter (fun j : Fin d => j ≤ k) with hS
  have hcard : S.card ≤ d := (Finset.card_le_univ S).trans_eq (Fintype.card_fin d)
  calc m ^ d ≤ m ^ S.card := pow_le_pow_of_le_one hm0.le hm1 hcard
    _ = m ^ S.card * 1 := (mul_one _).symm
    _ ≤ m ^ S.card * ∏ j ∈ S, ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hone (by positivity)
    _ = ∏ j ∈ S, m * ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ ∏ j ∈ S, ‖gs (fun i => fB B (e i)) j‖ ^ 2 :=
        Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hterm j)

end ReciprocityTheory.ReducedBases.T2

end
