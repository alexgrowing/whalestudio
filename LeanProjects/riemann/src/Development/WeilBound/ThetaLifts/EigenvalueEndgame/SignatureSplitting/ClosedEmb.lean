import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.ConvCont

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups

section Ring

variable {R : Type} [CommRing R]

def uni : Multiplicative R →* SL(2, R) where
  toFun x := ⟨!![1, x.toAdd; 0, 1], by simp⟩
  map_one' := Subtype.ext (by simp [Matrix.one_fin_two])
  map_mul' x y := Subtype.ext (by
    change _ = !![1, x.toAdd; 0, 1] * !![1, y.toAdd; 0, 1]
    simp [add_comm])

def dia : Rˣ →* SL(2, R) where
  toFun u := ⟨!![u.1, 0; 0, (u⁻¹).1], by simp⟩
  map_one' := Subtype.ext (by simp [Matrix.one_fin_two])
  map_mul' x y := Subtype.ext (by
    change _ = !![x.1, 0; 0, (x⁻¹).1] * !![y.1, 0; 0, (y⁻¹).1]
    simp [mul_comm])

theorem uni_val (x : Multiplicative R) : (uni x).1 = !![1, x.toAdd; 0, 1] := rfl

theorem dia_val (u : Rˣ) : (dia u).1 = !![u.1, 0; 0, (u⁻¹).1] := rfl

theorem uni_dia (x : R) (u : Rˣ) : uni (.ofAdd x) * dia u = dia u * uni (.ofAdd ((u⁻¹).1 * (u⁻¹).1 * x)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, uni_val, dia_val, Matrix.mul_fin_two, toAdd_ofAdd]
  congr 3
  all_goals simp only [mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_comm]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_uni : Continuous (uni : Multiplicative R → SL(2, R)) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_toAdd]) _

theorem closedEmb [T2Space R] : IsClosedEmbedding (Subtype.val : SL(2, R) → Matrix (Fin 2) (Fin 2) R) :=
  (isClosed_eq (continuous_id.matrix_det) continuous_const).isClosedEmbedding_subtypeVal

theorem box [T2Space R] {C : Fin 2 → Fin 2 → Set R} (h : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : SL(2, R) | ∀ i j, g.1 i j ∈ C i j} :=
  closedEmb.isCompact_preimage (isCompact_pi_infinite fun i => isCompact_pi_infinite (h i))

theorem nhds_box {W : Set SL(2, R)} (hW : W ∈ 𝓝 1) : ∃ O ∈ 𝓝 (0 : R), ∀ y : SL(2, R), (∀ i j, (y.1 - 1) i j ∈ O) → y ∈ W := by
  obtain ⟨O₁, h1, h2⟩ := (mem_nhds_subtype _ _ _).1 hW
  have h3 : (fun M : Fin 2 → Fin 2 → R => Matrix.of M + 1) ⁻¹' O₁ ∈ 𝓝 0 :=
    ((show Continuous (Matrix.of : (Fin 2 → Fin 2 → R) → _) from continuous_id).add continuous_const).continuousAt.preimage_mem_nhds
      (by change O₁ ∈ 𝓝 ((0 : Matrix (Fin 2) (Fin 2) R) + 1); rw [zero_add]; exact h1)
  rw [nhds_pi, Filter.mem_pi] at h3
  obtain ⟨I, -, t, h4, h5⟩ := h3
  simp only [nhds_pi, Filter.mem_pi] at h4
  choose J _ s h6 h7 using h4
  refine ⟨⋂ i, ⋂ j, s i j, by simpa using h6, fun y hy => h2 ?_⟩
  have := h5 (a := fun i j => (y.1 - 1) i j) fun i _ => h7 i fun j _ => Set.mem_iInter₂.1 (hy i j) i j
  change Matrix.of (fun i j => (y.1 - 1) i j) + 1 ∈ O₁ at this
  rwa [show Matrix.of (fun i j => (y.1 - 1) i j) = y.1 - 1 from rfl, sub_add_cancel] at this

theorem gauge {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q) {L : AddSubgroup Λ} (Lo : IsOpen (L : Set Λ)) :
    ∃ d : R → ℝ, Continuous d ∧ d 0 = 0 ∧ (∀ x, 0 ≤ d x) ∧ (∀ x y, q (x - y) ∈ L → |d x - d y| ≤ ‖p (x - y)‖) ∧
      ∀ x, ∀ ε ≤ 1 / 2, d x ≤ ε → ‖p x‖ ≤ ε ∧ q x ∈ L := by
  classical
  let d : R → ℝ := fun x => ‖p x‖ + if q x ∈ L then 0 else 1
  have d0 : ∀ x, 0 ≤ d x := fun x => add_nonneg (norm_nonneg _) (by split_ifs <;> simp)
  have dc : Continuous d := hp.norm.add ((IsLocallyConstant.continuous (f := fun z : Λ => if z ∈ L then (0 : ℝ) else 1)
    ((IsLocallyConstant.iff_eventually_eq _).2 fun z => by
      by_cases hz : z ∈ L
      · filter_upwards [Lo.mem_nhds hz] with w hw
        simp [hz, show w ∈ L from hw]
      · filter_upwards [(L.isClosed_of_isOpen Lo).isOpen_compl.mem_nhds hz] with w hw
        simp [hz, show w ∉ L from hw])).comp hq)
  have dt : ∀ x y, q (x - y) ∈ L → |d x - d y| ≤ ‖p (x - y)‖ := fun x y h => by
    have : q x ∈ L ↔ q y ∈ L := by
      rw [map_sub] at h
      exact ⟨fun a => by simpa using sub_mem a h, fun a => by simpa using add_mem h a⟩
    simp only [d, this, add_sub_add_right_eq_sub, map_sub]
    exact abs_norm_sub_norm_le _ _
  refine ⟨d, dc, by simp [d], d0, dt, fun x ε h3 h2 => ?_⟩
  have h4 := norm_nonneg (p x)
  simp only [d] at h2
  split_ifs at h2 with h
  · exact ⟨by linarith, h⟩
  · linarith

theorem diff_uni (κ y : SL(2, R)) (w : R) :
    (κ⁻¹ * y).1 - (κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y)).1 = w • ((κ⁻¹).1 * !![0, 1; 0, 0] * y.1) := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_sub, Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.smul_mul]
  congr 1
  conv_lhs => enter [1]; rw [← Matrix.one_mul y.1]
  rw [← Matrix.sub_mul, uni_val]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem nil_uni (y : SL(2, R)) (w : R) : !![0, 1; 0, 0] * ((uni (.ofAdd w))⁻¹ * y).1 = !![0, 1; 0, 0] * y.1 := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, uni_val]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

theorem bump_ex [T2Space R] {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q)
    (hc : ∀ (r : ℝ) (C : Set Λ), IsCompact C → IsCompact {x | ‖p x‖ ≤ r ∧ q x ∈ C})
    (hn : ∀ O ∈ 𝓝 (0 : R), ∃ ε > 0, ∃ U ∈ 𝓝 (0 : Λ), ∀ x, ‖p x‖ ≤ ε → q x ∈ U → x ∈ O)
    (hL : ∀ U ∈ 𝓝 (0 : Λ), ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ IsCompact (L : Set Λ) ∧ (L : Set Λ) ⊆ U)
    {W : Set SL(2, R)} (hW : W ∈ 𝓝 1) : ∃ η, Bump W η ∧ ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ ∀ (y y' : SL(2, R)) (b : ℝ),
      (∀ i j, q ((y.1 - y'.1) i j) ∈ L ∧ ‖p ((y.1 - y'.1) i j)‖ ≤ b) → |η y' - η y| ≤ 4 * b := by
  classical
  obtain ⟨O, hO, hOW⟩ := nhds_box hW
  obtain ⟨ε₀, h0, U, hU, hO'⟩ := hn O hO
  obtain ⟨L, Lo, Lc, LU⟩ := hL U hU
  obtain ⟨ε, ε0, ε1, ε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε ≤ 1 / 2 := ⟨_, lt_min h0 one_half_pos, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨d, dc, d00, d0, dt, dl⟩ := gauge p q hp hq Lo
  obtain ⟨e, he⟩ : ∃ e : SL(2, R) → ℝ, ∀ y, e y = ∑ i, ∑ j, d ((y.1 - 1) i j) := ⟨_, fun _ => rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : SL(2, R) → ℝ, ∀ y, η y = max (ε - e y) 0 := ⟨_, fun _ => rfl⟩
  have ec : Continuous e := by
    rw [funext he]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    dc.comp ((continuous_subtype_val.sub continuous_const).matrix_elem i j)
  have hs : ∀ y ∈ tsupport η, ∀ i j, ‖p ((y.1 - 1) i j)‖ ≤ ε ∧ q ((y.1 - 1) i j) ∈ L := fun y hy i j => by
    have h1 : e y ≤ ε := closure_minimal (s := Function.support η) (t := {y | e y ≤ ε})
      (fun z hz => le_of_not_gt fun h : ε < e z => hz ((hη z).trans (max_eq_right (by linarith))))
      (isClosed_le ec continuous_const) hy
    have h2 : d ((y.1 - 1) i j) ≤ ε :=
      ((Finset.single_le_sum (f := fun j => d ((y.1 - 1) i j)) (fun _ _ => d0 _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, d ((y.1 - 1) i j)) (fun _ _ => Finset.sum_nonneg fun _ _ => d0 _)
          (Finset.mem_univ i))).trans (he y ▸ h1)
    exact dl _ ε ε2 h2
  have hcs : HasCompactSupport η :=
    (box fun i j => (hc ε L Lc).image (continuous_add_const ((1 : Matrix (Fin 2) (Fin 2) R) i j))).of_isClosed_subset
      (isClosed_tsupport _) fun y hy i j => ⟨_, hs y hy i j, by simp⟩
  have ηc : Continuous η := by rw [funext hη]; exact (continuous_const.sub ec).max continuous_const
  refine ⟨η, ⟨ηc, hcs, fun y hy => hOW y fun i j => hO' _ ((hs y hy i j).1.trans ε1) (LU (hs y hy i j).2),
    fun y => (le_max_right _ _).trans_eq (hη y).symm, ?_⟩, L, Lo, fun y y' b hb => ?_⟩
  · have : e 1 = 0 := by simp [he, d00]
    simp only [hη, this, sub_zero, max_eq_left ε0.le]
    exact ε0.ne'
  rw [hη, hη]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [sub_sub_sub_cancel_left]
  simp only [he, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (g := fun _ => b) fun j _ => ?_)).trans_eq (by simp; ring))
  have e2 : (y.1 - 1) i j - (y'.1 - 1) i j = (y.1 - y'.1) i j := by rw [← Matrix.sub_apply, sub_sub_sub_cancel_right]
  exact (dt _ _ (e2 ▸ (hb i j).1)).trans (e2 ▸ (hb i j).2)

theorem lip_of [T2Space R] {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q)
    (hc : ∀ (r : ℝ) (C : Set Λ), IsCompact C → IsCompact {x | ‖p x‖ ≤ r ∧ q x ∈ C})
    (hn : ∀ O ∈ 𝓝 (0 : R), ∃ ε > 0, ∃ U ∈ 𝓝 (0 : Λ), ∀ x, ‖p x‖ ≤ ε → q x ∈ U → x ∈ O) {Γ : Subgroup SL(2, R)}
    (hL : ∀ U ∈ 𝓝 (0 : Λ), ∃ L : AddSubgroup Λ, IsOpen (L : Set Λ) ∧ IsCompact (L : Set Λ) ∧ (L : Set Λ) ⊆ U ∧
      ∃ D : ℝ, ∀ x : R, ∃ ξ, uni (.ofAdd ξ) ∈ Γ ∧ ‖p (ξ + x)‖ ≤ D ∧ q (ξ + x) ∈ L)
    {u : Rˣ} (hu : ‖p (u⁻¹).1‖ ≤ 1 / 2) (hu' : q (u⁻¹).1 = 1) (W : Set SL(2, R)) (hW : W ∈ 𝓝 1) :
    ∃ η, Bump W η ∧ ∀ Ω : Set SL(2, R), IsCompact Ω → ∃ (D : ℝ) (Ω' : Set SL(2, R)), IsCompact Ω' ∧ ∀ x (k : ℕ),
      ∃ γ ∈ Γ, ∃ v ∈ Ω', γ * uni x * dia u ^ k = dia u ^ k * v ∧
        ∀ κ ∈ Ω, ∀ y, |η (κ⁻¹ * (v⁻¹ * y)) - η (κ⁻¹ * y)| ≤ D / 2 ^ k := by
  obtain ⟨η, hη, L, Lo, hlip⟩ := bump_ex p q hp hq hc hn (fun U hU => (hL U hU).imp fun L h => ⟨h.1, h.2.1, h.2.2.1⟩) hW
  refine ⟨η, hη, fun Ω hΩ => ?_⟩
  obtain ⟨T, hT0⟩ : ∃ T : SL(2, R) × SL(2, R) → Matrix (Fin 2) (Fin 2) R, ∀ z, T z = (z.1⁻¹).1 * !![0, 1; 0, 0] * (z.1 * z.2).1 :=
    ⟨_, fun _ => rfl⟩
  have Tc : Continuous T := by
    rw [funext hT0]
    have c : Continuous (Subtype.val : SL(2, R) → Matrix (Fin 2) (Fin 2) R) := continuous_subtype_val
    have c1 : Continuous fun z : SL(2, R) × SL(2, R) => (z.1⁻¹).1 := c.comp (continuous_inv (G := SL(2, R)) |>.comp continuous_fst)
    have c2 : Continuous fun z : SL(2, R) × SL(2, R) => (z.1 * z.2).1 := c.comp (continuous_mul (M := SL(2, R)))
    exact (c1.matrix_mul continuous_const).matrix_mul c2
  have hC : IsCompact (⋃ i, ⋃ j, (fun z => T z i j) '' Ω ×ˢ tsupport η) :=
    isCompact_iUnion fun i => isCompact_iUnion fun j => (hΩ.prod hη.cpt).image (Tc.matrix_elem i j)
  obtain ⟨D₁, hD₁⟩ := hC.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨L', -, Lc', LU', D, hD⟩ := hL _ (hC.eventually_forall_of_forall_eventually (x₀ := (0 : Λ)) (P := fun z t => z * q t ∈ L)
    fun t _ => (continuous_fst.mul (hq.comp continuous_snd)).continuousAt.preimage_mem_nhds (Lo.mem_nhds (by simp)))
  refine ⟨4 * (D * max D₁ 0), uni '' (Multiplicative.ofAdd '' {x | ‖p x‖ ≤ D ∧ q x ∈ L'}),
    ((hc D L' Lc').image continuous_ofAdd).image continuous_uni, fun x k => ?_⟩
  obtain ⟨ξ, h1, h2, h3⟩ := hD x.toAdd
  have D0 : 0 ≤ D := (norm_nonneg _).trans h2
  obtain ⟨w, hw⟩ : ∃ w, w = ((u ^ k)⁻¹).1 * ((u ^ k)⁻¹).1 * (ξ + x.toAdd) := ⟨_, rfl⟩
  have w1 : ‖p w‖ ≤ D / 2 ^ k := by
    have a : ∀ z : V, ‖p ((u ^ k)⁻¹).1 * z‖ ≤ ‖z‖ / 2 ^ k := fun z => by
      rw [← inv_pow, Units.val_pow_eq_pow_val, map_pow]
      clear hw
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_assoc, pow_succ', ← div_div, div_right_comm, div_eq_inv_mul]
        exact (norm_mul_le _ _).trans (mul_le_mul (hu.trans_eq (one_div _)) ih (norm_nonneg _) (by positivity))
    rw [hw, map_mul, map_mul, mul_assoc]
    refine (a _).trans (div_le_div_of_nonneg_right ((a _).trans ((div_le_self (norm_nonneg _) (one_le_pow₀ one_le_two)).trans h2))
      (by positivity))
  have w2 : q w ∈ L' := by
    rwa [hw, map_mul, map_mul, ← inv_pow, Units.val_pow_eq_pow_val, map_pow, hu', one_pow, one_mul, one_mul]
  refine ⟨_, h1, _, ⟨_, ⟨w, ⟨w1.trans (div_le_self D0 (one_le_pow₀ one_le_two)), w2⟩, rfl⟩, rfl⟩, ?_, fun κ hκ y => ?_⟩
  · rw [← map_mul, ← map_pow, hw, ← uni_dia]; rfl
  have key : ∀ z ∈ tsupport η, T (κ, z) = (κ⁻¹).1 * !![0, 1; 0, 0] * y.1 →
      |η (κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y)) - η (κ⁻¹ * y)| ≤ 4 * (D * max D₁ 0) / 2 ^ k := fun z hz hT => by
    refine (hlip _ _ (D / 2 ^ k * max D₁ 0) fun i j => ?_).trans_eq (by ring)
    have m : T (κ, z) i j ∈ ⋃ i, ⋃ j, (fun z => T z i j) '' Ω ×ˢ tsupport η := Set.mem_iUnion₂.2 ⟨i, j, (κ, z), ⟨hκ, hz⟩, rfl⟩
    rw [diff_uni, ← hT, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul]
    exact ⟨LU' w2 _ m, (norm_mul_le _ _).trans (mul_le_mul w1 ((hD₁ _ m).trans (le_max_left _ _)) (norm_nonneg _) (by positivity))⟩
  by_cases a1 : κ⁻¹ * y ∈ tsupport η
  · exact key _ a1 (by simp only [hT0, mul_inv_cancel_left])
  by_cases a2 : κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y) ∈ tsupport η
  · exact key _ a2 (by simp only [hT0, mul_inv_cancel_left]; rw [Matrix.mul_assoc, nil_uni, Matrix.mul_assoc])
  · have b1 := image_eq_zero_of_notMem_tsupport a1
    have b2 := image_eq_zero_of_notMem_tsupport a2
    simp only [b1, b2, sub_self, abs_zero]
    positivity

end Ring

end PositivityTheory.ThKEnd.Two

end
