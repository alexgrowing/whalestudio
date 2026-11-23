import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaChol

noncomputable section

namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : ℕ}

def dp (p : Fin n → Fin n) (α β : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (if j = i then α i else 0) + (if j = p i then β i else 0)

theorem dp_mul_apply (p : Fin n → Fin n) (α β : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dp p α β * X) i j = α i * X i j + β i * X (p i) j := by
  simp [dp, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem dp_mul_dp {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (α β α' β' : Fin n → ℂ) :
    dp p α β * dp p α' β' =
      dp p (fun i => α i * α' i + β i * β' (p i)) (fun i => α i * β' i + β i * α' (p i)) := by
  ext i j
  rw [dp_mul_apply]
  simp only [dp, Matrix.of_apply, hp]
  split_ifs <;> ring

theorem dp_conjTranspose {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (α β : Fin n → ℂ) :
    (dp p α β)ᴴ = dp p (fun i => star (α i)) (fun i => star (β (p i))) := by
  ext i j
  simp only [dp, conjTranspose_apply, Matrix.of_apply, star_add]
  congr 1
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · by_cases h : j = p i
    · subst h; simp [hp]
    · have : i ≠ p j := fun h' => h (by rw [h', hp])
      simp [h, this]

theorem dp_congr {p : Fin n → Fin n} {α β α' β' : Fin n → ℂ}
    (h1 : ∀ i, p i = i → α i + β i = α' i + β' i) (h2 : ∀ i, p i ≠ i → α i = α' i ∧ β i = β' i) :
    dp p α β = dp p α' β' := by
  ext i j
  simp only [dp, Matrix.of_apply]
  by_cases h : p i = i
  · rw [h]
    split_ifs
    · exact h1 i h
    · rfl
  · rw [(h2 i h).1, (h2 i h).2]

theorem dp_diagonal (p : Fin n → Fin n) (α : Fin n → ℂ) : dp p α 0 = diagonal α := by
  ext i j
  by_cases h : i = j
  · subst h; simp [dp]
  · simp [dp, h, Ne.symm h]

theorem mul_dp_apply {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (β : Fin n → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : (X * dp p 0 β) i j = X i (p j) * β (p j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (p j)]
  · simp [dp, hp]
  · intro k _ hk
    have : j ≠ p k := fun h => hk (by rw [h, hp])
    simp [dp, this]
  · simp

theorem eq_zero_of_unitary_blockTriangular {b : Fin n → ℤ} {w : Matrix (Fin n) (Fin n) ℂ}
    (h1 : wᴴ * w = 1) (hw : w.BlockTriangular b) {i j : Fin n} (hij : b i ≠ b j) : w i j = 0 := by
  let _ : Invertible w := invertibleOfLeftInverse w wᴴ h1
  have hinv : w⁻¹ = wᴴ := inv_eq_left_inv h1
  have h2 : w⁻¹.BlockTriangular b := blockTriangular_inv_of_blockTriangular hw
  rw [hinv] at h2
  rcases lt_or_gt_of_ne hij with h | h
  · have := h2 h
    simpa [conjTranspose_apply] using this
  · exact hw h

theorem eq_one_of_posSemidef {w : Matrix (Fin n) (Fin n) ℂ} (h1 : wᴴ * w = 1) (hw : w.PosSemidef) : w = 1 := by
  rw [hw.isHermitian.eq] at h1
  have hu : IsUnit (1 + w) := (PosDef.one.add_posSemidef hw).isUnit
  have : (1 + w) * (w - 1) = 0 := by
    rw [mul_sub, add_mul, h1]; simp [add_comm]
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

structure Adapted (p : Fin n → Fin n) (b : Fin n → ℤ) (c : Fin n → ℂ) : Prop where
  invol : ∀ i, p (p i) = i
  mono : Monotone b
  neg : ∀ i, b (p i) = -b i
  fix : ∀ i, b i = 0 → p i = i
  inj : ∀ i j, b i ≠ 0 → b i = b j → i = j
  sq : ∀ i, c i * c i = 1
  star_eq : ∀ i, star (c i) = c i
  symm : ∀ i, c (p i) = c i
  mid : ∀ i j, b i = 0 → b j = 0 → c i = c j

variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}

theorem Adapted.mul_self (h : Adapted p b c) : dp p 0 c * dp p 0 c = 1 := by
  rw [dp_mul_dp h.invol, ← diagonal_one, ← dp_diagonal p]
  congr 1 <;> funext i <;> simp [h.symm, h.sq]

theorem Adapted.herm (h : Adapted p b c) : (dp p 0 c)ᴴ = dp p 0 c := by
  rw [dp_conjTranspose h.invol]
  congr 1 <;> funext i <;> simp only [h.symm, h.star_eq, Pi.zero_apply, star_zero]

theorem Adapted.conj_apply (h : Adapted p b c) (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dp p 0 c * Bᴴ * dp p 0 c) i j = c i * c j * star (B (p j) (p i)) := by
  rw [mul_dp_apply h.invol, dp_mul_apply, h.symm, conjTranspose_apply, conjTranspose_apply]
  simp only [Pi.zero_apply]
  ring

theorem Adapted.tri (h : Adapted p b c) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.BlockTriangular id) :
    B.BlockTriangular b := fun _ _ hij => hB (h.mono.reflect_lt hij)

theorem Adapted.conj_tri (h : Adapted p b c) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.BlockTriangular id) :
    (dp p 0 c * Bᴴ * dp p 0 c).BlockTriangular b := by
  intro i j hij
  rw [h.conj_apply, h.tri hB (by rw [h.neg, h.neg]; omega)]
  simp

theorem Adapted.posSemidef (h : Adapted p b c) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.BlockTriangular id)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hBa : ∀ i, B i i = a i)
    (hz : ∀ i j, b i ≠ b j → (B * (dp p 0 c * Bᴴ * dp p 0 c)) i j = 0) :
    (B * (dp p 0 c * Bᴴ * dp p 0 c)).PosSemidef := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if b i = 0 ∧ b j = 0 then B i j else 0 with hE
  set d : Fin n → ℂ := fun i => if b i = 0 then 0 else ((a i * a (p i) : ℝ) : ℂ) with hd
  have key : B * (dp p 0 c * Bᴴ * dp p 0 c) = diagonal d + E * Eᴴ := by
    ext i j
    rw [Matrix.add_apply]
    by_cases hij : b i = b j
    · have hterm : ∀ k, b k ≠ b i → B i k * (dp p 0 c * Bᴴ * dp p 0 c) k j = 0 := by
        intro k hk
        rcases lt_or_gt_of_ne hk with h' | h'
        · rw [h.tri hB h', zero_mul]
        · rw [h.conj_tri hB (by omega), mul_zero]
      by_cases hi : b i = 0
      · have hj : b j = 0 := hij ▸ hi
        have hdiag : diagonal d i j = 0 := by
          by_cases e : i = j
          · subst e; simp [hd, hi]
          · simp [e]
        rw [hdiag, zero_add, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : b k = 0
        · rw [h.conj_apply, h.mid k j hk hj, h.sq, h.fix j hj, h.fix k hk]
          simp [hE, hi, hj, hk]
        · rw [hterm k (by omega)]
          simp [hE, hk]
      · obtain rfl := h.inj i j hi hij
        have hEE : (E * Eᴴ) i i = 0 := by simp [Matrix.mul_apply, hE, hi]
        rw [hEE, add_zero, Matrix.mul_apply, Finset.sum_eq_single i]
        · rw [h.conj_apply, h.sq, hBa, hBa]
          simp [hd, hi]
        · intro k _ hk
          exact hterm k fun e => hk (h.inj i k hi e.symm).symm
        · simp
    · have e : i ≠ j := fun e => hij (e ▸ rfl)
      rw [hz i j hij, diagonal_apply_ne _ e, zero_add, Matrix.mul_apply]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hi : b i = 0
      · have hj : b j ≠ 0 := by omega
        simp [hE, hj]
      · simp [hE, hi]
  rw [key]
  refine PosSemidef.add (posSemidef_diagonal_iff.2 fun i => ?_) (posSemidef_self_mul_conjTranspose E)
  simp only [hd]
  split_ifs
  · exact le_rfl
  · exact_mod_cast (mul_pos (ha i) (ha (p i))).le

def Dec (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * H * g = H →
    ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ s : Matrix (Fin n) (Fin n) ℂ, kᴴ * H * k = H ∧ sᴴ * H * s = H ∧
      g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

theorem flip {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hg : gᴴ * A * g = A) : g * A * gᴴ = A := by
  have h1 : (A * gᴴ * A) * g = 1 := by
    calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hA]
  have h2 : g * (A * gᴴ * A) = 1 := mul_eq_one_comm.1 h1
  calc g * A * gᴴ = g * A * gᴴ * (A * A) := by rw [hA, Matrix.mul_one]
    _ = (g * (A * gᴴ * A)) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h2, Matrix.one_mul]

theorem Adapted.dec (h : Adapted p b c) : Dec (dp p 0 c) := by
  refine ⟨1, one_mem _, fun g hg => ?_⟩
  set A := dp p 0 c with hAdef
  have hA : A * A = 1 := h.mul_self
  have hAH : Aᴴ = A := h.herm
  have hg' : g * A * gᴴ = A := flip hA hg
  have hgu : IsUnit g := by
    refine ⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩
    · calc g * (A * gᴴ * A) = (g * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hA]
    · calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hA]
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ :=
    exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact RCLike.ofReal_ne_zero.2 (ha i).ne')
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hBiH : B⁻¹ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBi', conjTranspose_one]

  have hS : Bᴴ * B * A * (Bᴴ * B) = A := by
    rw [hBS]
    calc gᴴ * g * A * (gᴴ * g) = gᴴ * (g * A * gᴴ) * g := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hg', hg]
  have hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1 := by
    calc A * (Bᴴ * B) * A * Bᴴ * B = A * (Bᴴ * B * A * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, hA]
  have hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1 := mul_eq_one_comm.1 hS1
  have hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1 := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
    calc A * (B * A) * Bᴴ * (B * (A * Bᴴ * A)) = A * (B * (A * (Bᴴ * B) * A * Bᴴ)) * A := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, hA]
  have hw1 : B * (A * Bᴴ * A) = 1 :=
    eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij =>
      eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)
  have hw2 : (A * Bᴴ * A) * B = 1 := mul_eq_one_comm.1 hw1
  have hBA : Bᴴ * A * B = A := by
    calc Bᴴ * A * B = (A * A) * (Bᴴ * A * B) := by rw [hA, Matrix.one_mul]
      _ = A * ((A * Bᴴ * A) * B) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hw2, Matrix.mul_one]
  refine ⟨g * B⁻¹, ?_, B, ?_, hBA, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᴴ * Bᴴ) * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiH, hBi', Matrix.one_mul]
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * A * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * A * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * (Bᴴ * A * B) * B⁻¹ := by rw [hg, hBA]
      _ = (B⁻¹ᴴ * Bᴴ) * A * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hBiH, hBi', Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hBi, Matrix.mul_one]
  · rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]; exact hB

theorem Dec.of_conj {H V : Matrix (Fin n) (Fin n) ℂ} (hV : Vᴴ * V = 1) (h : Dec (Vᴴ * H * V)) : Dec H := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  have c1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, Vᴴ * (V * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have c2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, V * (Vᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hV', Matrix.one_mul]
  have hVu : V ∈ Matrix.unitaryGroup (Fin n) ℂ := mem_unitaryGroup_iff'.2 hV
  have hVu' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := Unitary.star_mem hVu
  have back : ∀ x : Matrix (Fin n) (Fin n) ℂ, xᴴ * (Vᴴ * H * V) * x = Vᴴ * H * V →
      (V * x * Vᴴ)ᴴ * H * (V * x * Vᴴ) = H := by
    intro x hx
    calc (V * x * Vᴴ)ᴴ * H * (V * x * Vᴴ) = V * (xᴴ * (Vᴴ * H * V) * x) * Vᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = H := by rw [hx]; simp only [Matrix.mul_assoc, c2, hV', Matrix.mul_one]
  obtain ⟨U, hU, h⟩ := h
  refine ⟨V * U, mul_mem hVu hU, fun g hg => ?_⟩
  obtain ⟨k, hk, s, hkH, hsH, hks, hs⟩ := h (Vᴴ * g * V) (by
    calc (Vᴴ * g * V)ᴴ * (Vᴴ * H * V) * (Vᴴ * g * V) = Vᴴ * (gᴴ * H * g) * V := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, c2]
      _ = _ := by rw [hg])
  refine ⟨V * k * Vᴴ, mul_mem (mul_mem hVu hk) hVu', V * s * Vᴴ, back k hkH, back s hsH, ?_, ?_⟩
  · calc g = V * (Vᴴ * g * V) * Vᴴ := by simp only [Matrix.mul_assoc, c2, hV', Matrix.mul_one]
      _ = _ := by rw [hks]; simp only [Matrix.mul_assoc, c1]
  · have : (V * U)ᴴ * (V * s * Vᴴ) * (V * U) = Uᴴ * s * U := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, c1]
    rw [this]; exact hs

end CompanionTheory.D.gk.admitted.CholeskyDecomposition
