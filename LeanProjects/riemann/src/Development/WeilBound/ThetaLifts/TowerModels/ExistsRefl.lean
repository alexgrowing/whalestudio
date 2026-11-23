import Mathlib

namespace PositivityTheory.ThKG.Tow.Levi

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def hf (M : Matrix n n ℂ) : (n → ℂ) →ₗ[ℂ] (n → ℂ) →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x ⬝ᵥ M *ᵥ star y)
    (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => smul_dotProduct _ _ _)
    (fun _ _ _ => by rw [star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [star_smul, mulVec_smul, dotProduct_smul]; rfl)

variable {M θ : Matrix n n ℂ}

omit [DecidableEq n] in
theorem hf_apply (x y : n → ℂ) : hf M x y = x ⬝ᵥ M *ᵥ star y := rfl

omit [DecidableEq n] in
theorem hf_mulVec (g : Matrix n n ℂ) (x y : n → ℂ) : hf M (g *ᵥ x) (g *ᵥ y) = hf (gᵀ * M * g.map star) x y := by
  have e : star (g *ᵥ y) = g.map star *ᵥ star y := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) g y i
  rw [hf_apply, hf_apply, e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

theorem iso_of_hf {g : Matrix n n ℂ} (h : ∀ x y, hf M (g *ᵥ x) (g *ᵥ y) = hf M x y) : gᵀ * M * g.map star = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_mulVec, hf_apply, hf_apply] at this
  simpa [← Pi.single_star] using this

omit [DecidableEq n] in
theorem hf_conj (hM : ∀ i j, star (M j i) = M i j) (x y : n → ℂ) : starRingEnd ℂ (hf M x y) = hf M y x := by
  simp only [hf_apply, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hM i j]
  simp [mul_comm, mul_left_comm]

theorem exists_refl (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {u u' : n → ℂ}
    (hu : θ *ᵥ u = ε • u) (hu' : θ *ᵥ u' = ε • u') (e : hf M u u = hf M u' u') :
    ∃ κ : Matrix n n ℂ, κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ u = u' ∧ ∀ z, θ *ᵥ z = -ε • z → κ *ᵥ z = z := by
  obtain ⟨a, ha⟩ : ∃ a, a = u - u' := ⟨_, rfl⟩
  have hθ : ∀ x y, hf M (θ *ᵥ x) (θ *ᵥ y) = hf M x y := fun x y => by rw [hf_mulVec, h2]
  have hθθ : ∀ x, θ *ᵥ (θ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h1, one_mulVec]
  have hεc : starRingEnd ℂ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hθa : θ *ᵥ a = ε • a := by rw [ha, mulVec_sub, hu, hu', smul_sub]
  have haa : hf M a a = hf M u a + starRingEnd ℂ (hf M u a) := by
    rw [hf_conj hM, ha]
    simp only [map_sub, LinearMap.sub_apply]
    rw [e]; ring
  obtain ⟨b, hb⟩ : ∃ b, b = hf M u a := ⟨_, rfl⟩
  rw [← hb] at haa
  let κ : Matrix n n ℂ := 1 - b⁻¹ • vecMulVec a (M *ᵥ star a)
  have hκ : ∀ z, κ *ᵥ z = z - (b⁻¹ * hf M z a) • a := fun z => by
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hf_apply, dotProduct_comm z]
    simp [mul_smul]
  refine ⟨κ, iso_of_hf fun z w => ?_, ?_, ?_, fun z hz => ?_⟩
  · rw [hκ, hκ]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, haa,
      map_mul, map_inv₀, hf_conj hM]
    by_cases h0 : b = 0
    · simp [h0]
    · have h0' : starRingEnd ℂ b ≠ 0 := by simpa using h0
      field_simp
      ring
  · refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    have : hf M (θ *ᵥ z) a = ε * hf M z a := by
      rw [← hθ, hθθ, hθa, LinearMap.map_smulₛₗ, hεc, smul_eq_mul]
    rw [toLin'_apply, toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, hκ, hκ, mulVec_sub, mulVec_smul, hθa, this, smul_smul]
    congr 2
    ring
  · rw [hκ, ← hb]
    by_cases h0 : b = 0
    · have : a = 0 := by
        by_contra hne
        have := h3 a hne
        rw [hθa, map_smul, LinearMap.smul_apply, haa, h0] at this
        simp at this
      rw [this, smul_zero, sub_zero]
      exact sub_eq_zero.1 (ha ▸ this)
    · rw [inv_mul_cancel₀ h0, one_smul, ha, sub_sub_cancel]
  · have : hf M z a = 0 := by
      have := hθ z a
      rw [hz, hθa, LinearMap.map_smulₛₗ, hεc, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
      linear_combination (-1 / 2 : ℂ) * this - (1 / 2 : ℂ) * hf M z a * hεε
    rw [hκ, this, mul_zero, zero_smul, sub_zero]

theorem exists_move (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {v v' : n → ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (e : hf M v v = 0) (e' : hf M v' v' = 0) :
    ∃ (κ : Matrix n n ℂ) (t : ℂ), t ≠ 0 ∧ κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ v = t • v' := by
  have hθ : ∀ x y, hf M (θ *ᵥ x) (θ *ᵥ y) = hf M x y := fun x y => by rw [hf_mulVec, h2]
  have hθθ : ∀ x, θ *ᵥ (θ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h1, one_mulVec]
  have hs : ∀ x, hf M x (θ *ᵥ x) = hf M (θ *ᵥ x) x := fun x => by rw [← hθ, hθθ]
  have hre : ∀ x, ((hf M (θ *ᵥ x) x).re : ℂ) = hf M (θ *ᵥ x) x := fun x =>
    Complex.conj_eq_iff_re.1 (by rw [hf_conj hM, hs])
  have p := h3 v hv
  have p' := h3 v' hv'
  let t : ℝ := Real.sqrt ((hf M (θ *ᵥ v) v).re / (hf M (θ *ᵥ v') v').re)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos p p')
  have htt : (t : ℂ) * t * hf M (θ *ᵥ v') v' = hf M (θ *ᵥ v) v := by
    rw [← hre v, ← hre v', ← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (div_pos p p').le,
      div_mul_cancel₀ _ p'.ne']
  obtain ⟨w, hw⟩ : ∃ w, w = (t : ℂ) • v' := ⟨_, rfl⟩
  have ew : hf M w w = 0 := by
    rw [hw, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, e', smul_zero, smul_zero]
  have ew' : hf M (θ *ᵥ w) w = hf M (θ *ᵥ v) v := by
    rw [hw, LinearMap.map_smulₛₗ, mulVec_smul, map_smul, LinearMap.smul_apply, Complex.conj_ofReal, ← htt, smul_eq_mul,
      smul_eq_mul, mul_assoc]
  have ep : ∀ x, θ *ᵥ (x + θ *ᵥ x) = (1 : ℂ) • (x + θ *ᵥ x) := fun x => by rw [mulVec_add, hθθ, one_smul, add_comm]
  have em : ∀ x, θ *ᵥ (x - θ *ᵥ x) = (-1 : ℂ) • (x - θ *ᵥ x) := fun x => by rw [mulVec_sub, hθθ, neg_one_smul, neg_sub]
  obtain ⟨κ₁, a1, a2, a3, a4⟩ := exists_refl hM h1 h2 h3 (Or.inl rfl) (ep v) (ep w) (by
    simp only [map_add, LinearMap.add_apply, hθ, hs, e, ew, ew'])
  obtain ⟨κ₂, b1, b2, b3, b4⟩ := exists_refl hM h1 h2 h3 (Or.inr rfl) (em v) (em w) (by
    simp only [map_sub, LinearMap.sub_apply, hθ, hs, e, ew, ew'])
  refine ⟨κ₂ * κ₁, t, by exact_mod_cast ht.ne', iso_of_hf fun x y => ?_, b2.mul_left a2, ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hf_mulVec, b1, hf_mulVec, a1]
  · have e1 : v = (2 : ℂ)⁻¹ • ((v + θ *ᵥ v) + (v - θ *ᵥ v)) := by module
    rw [← hw, ← mulVec_mulVec, e1, mulVec_smul, mulVec_add, a3, a4 _ (em v), mulVec_smul, mulVec_add, b3,
      b4 _ (by rw [neg_neg]; exact ep w)]
    module

end PositivityTheory.ThKG.Tow.Levi
