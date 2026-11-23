import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniLatA

open Matrix Filter Topology

namespace LevelTowerAlt.LocFin

variable {Λ : Type} [AddCommGroup Λ] {N m : ℕ}

noncomputable def coords (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) : Matrix (Fin m) (Fin N) ℤ :=
  Matrix.of fun i k => e.repr (v i) k

theorem repr_sum (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) (y : Fin m → ℤ) :
    (fun k => e.repr (∑ i, y i • v i) k) = (coords e v)ᵀ *ᵥ y := by
  funext k
  simp [coords, mulVec, dotProduct, map_sum, Finsupp.finset_sum_apply, mul_comm]

theorem eq_of_repr (e : Module.Basis (Fin N) ℤ Λ) {x y : Λ}
    (h : (fun k => e.repr x k) = fun k => e.repr y k) : x = y :=
  e.repr.injective (Finsupp.ext fun k => congrFun h k)

theorem det_ne_zero (e : Module.Basis (Fin N) ℤ Λ) {v : Fin m → Λ} (hv : LinearIndependent ℤ v) :
    (coords e v * (coords e v)ᵀ).det ≠ 0 := by
  intro h
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : ((coords e v)ᵀ *ᵥ y) ⬝ᵥ ((coords e v)ᵀ *ᵥ y) = 0 := by
    have : ((coords e v)ᵀ *ᵥ y) ⬝ᵥ ((coords e v)ᵀ *ᵥ y) = y ⬝ᵥ ((coords e v * (coords e v)ᵀ) *ᵥ y) := by
      rw [← mulVec_mulVec, dotProduct_mulVec y, ← mulVec_transpose]
    rw [this, hy, dotProduct_zero]
  have h2 : (coords e v)ᵀ *ᵥ y = 0 := dotProduct_self_eq_zero.1 h1
  have h3 : ∑ i, y i • v i = 0 := by
    apply eq_of_repr e
    rw [repr_sum, h2]
    funext k
    simp
  exact hy0 (funext (Fintype.linearIndependent_iff.1 hv y h3))

theorem exists_proj (e : Module.Basis (Fin N) ℤ Λ) {v : Fin m → Λ} {A : Set Λ}
    (hA : ∀ x, x ∈ A ↔ ∃ y : Fin m → ℤ, ∑ i, y i • v i = x)
    (hsat : ∀ (x : Λ) (n : ℤ), n ≠ 0 → n • x ∈ A → x ∈ A)
    (hd : 0 < (coords e v * (coords e v)ᵀ).det) :
    ∃ Q : Matrix (Fin N) (Fin N) ℤ, (∀ i j, |Q i j| ≤ (coords e v * (coords e v)ᵀ).det) ∧
      A = {x | Q *ᵥ (fun k => e.repr x k) = (coords e v * (coords e v)ᵀ).det • fun k => e.repr x k} := by
  obtain ⟨B, hB⟩ : ∃ B, B = coords e v := ⟨_, rfl⟩
  have hr := repr_sum e v
  rw [← hB] at hd hr ⊢
  obtain ⟨d, hdd⟩ : ∃ d, d = (B * Bᵀ).det := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hQB : Bᵀ * (B * Bᵀ).adjugate * B * Bᵀ = d • Bᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, adjugate_mul, ← hdd, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Bᵀ * (B * Bᵀ).adjugate * B := ⟨_, rfl⟩
  have hQQ : Q * Q = d • Q := by
    calc Q * Q = (Bᵀ * (B * Bᵀ).adjugate * B * Bᵀ) * ((B * Bᵀ).adjugate * B) := by
          rw [hQ]; simp only [Matrix.mul_assoc]
      _ = d • Q := by rw [hQB, hQ, Matrix.smul_mul, Matrix.mul_assoc]
  have hQt : Qᵀ = Q := by
    rw [hQ, transpose_mul, transpose_mul, transpose_transpose, adjugate_transpose, transpose_mul,
      transpose_transpose, Matrix.mul_assoc]
  refine ⟨Q, fun i j => ?_, ?_⟩
  · have h1 : ∑ k, Q i k ^ 2 = d * Q i i := by
      have := congrFun (congrFun hQQ i) i
      rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : Q k i = Q i k := by
        have := congrFun (congrFun hQt i) k
        rwa [transpose_apply] at this
      rw [this, sq]
    have h2 : ∀ k, Q i k ^ 2 ≤ d * Q i i := fun k => h1 ▸
      Finset.single_le_sum (f := fun k => Q i k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have h3 := h2 i
    have h4 := h2 j
    have h5 : Q i i ≤ d := by
      by_contra hc
      push Not at hc
      nlinarith
    have h6 : Q i j ^ 2 ≤ d ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq h6 hd.le
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := (hA x).1 hx
      rw [hr, mulVec_mulVec, hQ, hQB, smul_mulVec]
    · intro hx
      refine hsat x d hd.ne' ((hA _).2 ⟨((B * Bᵀ).adjugate * B) *ᵥ (fun k => e.repr x k), ?_⟩)
      apply eq_of_repr e
      rw [hr, mulVec_mulVec, ← Matrix.mul_assoc, ← hQ, hx]
      funext k
      simp

theorem finite_sat (e : Module.Basis (Fin N) ℤ Λ) (T : ℤ) :
    {A : Set Λ | ∃ (m : ℕ) (v : Fin m → Λ), (∀ x, x ∈ A ↔ ∃ y : Fin m → ℤ, ∑ i, y i • v i = x) ∧
      (∀ (x : Λ) (n : ℤ), n ≠ 0 → n • x ∈ A → x ∈ A) ∧ 0 < (coords e v * (coords e v)ᵀ).det ∧
      (coords e v * (coords e v)ᵀ).det ≤ T}.Finite := by
  have h1 : {Q : Fin N → Fin N → ℤ | ∀ i, Q i ∈ {r : Fin N → ℤ | ∀ j, r j ∈ Set.Icc (-T) T}}.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Set.finite_Icc _ _
  have h2 := ((Set.finite_Icc 0 T).prod h1).image
    (fun p : ℤ × (Fin N → Fin N → ℤ) =>
      {x : Λ | (Matrix.of p.2) *ᵥ (fun k => e.repr x k) = p.1 • fun k => e.repr x k})
  refine h2.subset ?_
  rintro A ⟨m, v, hA, hsat, hd, hT⟩
  obtain ⟨Q, hQ, hAQ⟩ := exists_proj e hA hsat hd
  refine ⟨(_, Matrix.of.symm Q), ⟨⟨hd.le, hT⟩, fun i j => ?_⟩, hAQ.symm⟩
  exact abs_le.1 ((hQ i j).trans hT)

theorem unif_pos (S0 : Matrix (Fin N) (Fin N) ℝ) (h0 : ∀ x : Fin N → ℝ, x ≠ 0 → 0 < x ⬝ᵥ S0 *ᵥ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ S in 𝓝 S0, ∀ x : Fin N → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ S *ᵥ x := by
  have hc : Continuous fun z : (ℝ × Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) =>
      z.2 ⬝ᵥ z.1.2 *ᵥ z.2 - z.1.1 * (z.2 ⬝ᵥ z.2) :=
    (continuous_snd.dotProduct ((continuous_snd.comp continuous_fst).matrix_mulVec continuous_snd)).sub
      ((continuous_fst.comp continuous_fst).mul (continuous_snd.dotProduct continuous_snd))
  have h1 := (isCompact_sphere (0 : Fin N → ℝ) 1).eventually_forall_of_forall_eventually
    (x₀ := ((0 : ℝ), S0)) (P := fun p x => 0 < x ⬝ᵥ p.2 *ᵥ x - p.1 * (x ⬝ᵥ x)) (fun y hy => by
      have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      refine hc.continuousAt.eventually (lt_mem_nhds ?_)
      simpa using h0 y hy0)
  have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ᶠ S in 𝓝 S0, ∀ x ∈ Metric.sphere (0 : Fin N → ℝ) 1,
      0 < x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x) := h1.curry_nhds.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hc1, hc0⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨c, hc0, hc1.mono fun S hS x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h3 := hS (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h3
  have h4 : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x)) := by linarith
  have h5 := (mul_pos_iff_of_pos_left (by positivity)).1 h4
  linarith

theorem det_bound (B : Matrix (Fin m) (Fin N) ℤ) (hB : (B * Bᵀ).det ≠ 0) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : Sᵀ = S) {c : ℝ} (hc : 0 < c) (h : ∀ x : Fin N → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ S *ᵥ x) :
    0 < (B * Bᵀ).det ∧ c ^ m * ((B * Bᵀ).det : ℝ) ≤
      (B.map (Int.castRingHom ℝ) * S * (B.map (Int.castRingHom ℝ))ᵀ).det := by
  obtain ⟨Br, hBr⟩ : ∃ Br, Br = B.map (Int.castRingHom ℝ) := ⟨_, rfl⟩
  have hdet : ((B * Bᵀ).det : ℝ) = (Br * Brᵀ).det := by
    have := (Int.castRingHom ℝ).map_det (B * Bᵀ)
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, ← hBr] at this
    exact this
  rw [← hBr]
  have hpsd : (Br * Brᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose Br
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hne : (Br * Brᵀ).det ≠ 0 := by
    rw [← hdet]; exact_mod_cast hB
  have hpd : (Br * Brᵀ).PosDef :=
    hpsd.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
  have hpos : 0 < (Br * Brᵀ).det := hpd.det_pos
  refine ⟨by rw [← hdet] at hpos; exact_mod_cast hpos, ?_⟩
  have h1 : (S - c • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, hS, transpose_smul, transpose_one]
    · have := h x
      simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      linarith
  have h2 := h1.mul_mul_conjTranspose_same Br
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul] at h2
  have h3 := ReciprocityTheory.L2DbarEstimates.Y.uniLat_det_le_of_sub (hpd.smul hc) h2
  rwa [det_smul, Fintype.card_fin, ← hdet] at h3

end LevelTowerAlt.LocFin
