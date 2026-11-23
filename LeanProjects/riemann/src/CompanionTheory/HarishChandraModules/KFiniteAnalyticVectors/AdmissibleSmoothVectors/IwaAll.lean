import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

noncomputable section

namespace CompanionTheory.D.gk.admitted

open Matrix PI.UpqRep

namespace CholeskyDecomposition

variable {n : ℕ}

def pr (ε : Fin n → Bool) (i : Fin n) : Fin n := if ε i.rev = ε i then i else i.rev

def ht (ε : Fin n → Bool) (i : Fin n) : ℤ := if ε i.rev = ε i then 0 else 2 * (i : ℤ) + 1 - n

def sg (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1

def wt (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i.rev = ε i then sg ε i else 1

theorem pr_pr (ε : Fin n → Bool) (i : Fin n) : pr ε (pr ε i) = i := by
  unfold pr
  by_cases h : ε i.rev = ε i
  · simp [h]
  · have h' : ¬ε i = ε i.rev := fun e => h e.symm
    simp [h, h']

theorem rev_cast (i : Fin n) : ((i.rev : Fin n) : ℤ) = n - 1 - i := by
  have h1 := Fin.val_rev i
  have h2 := i.isLt
  omega

theorem ht_ne {ε : Fin n → Bool} {i : Fin n} (h : ε i.rev ≠ ε i) : 2 * (i : ℤ) + 1 - n ≠ 0 := by
  intro h2
  apply h
  have e : i.rev = i := by
    ext
    have h3 := Fin.val_rev i
    omega
  rw [e]

theorem ht_eq_zero {ε : Fin n → Bool} {i : Fin n} : ht ε i = 0 ↔ ε i.rev = ε i := by
  unfold ht
  by_cases h : ε i.rev = ε i
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun e => absurd e (ht_ne h), fun e => absurd e h⟩

theorem lt_of_sign {ε : Fin n → Bool} (hε : Monotone ε) {i j : Fin n} (hi : ε i = false) (hj : ε j = true) :
    (i : ℤ) < j := by
  by_contra hc
  have hji : j ≤ i := by
    rw [Fin.le_iff_val_le_val]
    omega
  have h3 := hε hji
  rw [hi, hj] at h3
  exact absurd h3 (by decide)

theorem adapted {ε : Fin n → Bool} (hε : Monotone ε) : Adapted (pr ε) (ht ε) (wt ε) := by
  have hpos : ∀ i : Fin n, ε i = true → ε i.rev = false → 0 < 2 * (i : ℤ) + 1 - n := by
    intro i h1 h2
    have h3 := lt_of_sign hε h2 h1
    rw [rev_cast] at h3
    linarith
  have hneg : ∀ i : Fin n, ε i = false → ε i.rev = true → 2 * (i : ℤ) + 1 - n < 0 := by
    intro i h1 h2
    have h3 := lt_of_sign hε h1 h2
    rw [rev_cast] at h3
    linarith
  refine ⟨pr_pr ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 : ε i ≤ ε j := hε hij
    have h2 : ε j.rev ≤ ε i.rev := hε (Fin.rev_le_rev.mpr hij)
    have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
    unfold ht
    split_ifs with a b b
    · exact le_refl _
    · have key : ∀ x y z w : Bool, x ≤ z → w ≤ y → y = x → ¬w = z → z = true ∧ w = false := by
        intro x y z w
        cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })
      obtain ⟨hz, hw⟩ := key _ _ _ _ h1 h2 a b
      exact (hpos j hz hw).le
    · have key : ∀ x y z w : Bool, x ≤ z → w ≤ y → ¬y = x → w = z → x = false ∧ y = true := by
        intro x y z w
        cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })
      obtain ⟨hx, hy⟩ := key _ _ _ _ h1 h2 a b
      exact (hneg i hx hy).le
    · linarith
  · intro i
    unfold ht pr
    by_cases h : ε i.rev = ε i
    · simp [h]
    · have h' : ¬ε i = ε i.rev := fun e => h e.symm
      simp only [h, h', ↓reduceIte, Fin.rev_rev]
      rw [rev_cast]
      ring
  · intro i h
    have h' := ht_eq_zero.mp h
    unfold pr
    rw [if_pos h']
  · intro i j hi hij
    have hi' : ¬ε i.rev = ε i := fun e => hi (ht_eq_zero.mpr e)
    have hj' : ¬ε j.rev = ε j := fun e => hi (hij.trans (ht_eq_zero.mpr e))
    unfold ht at hij
    rw [if_neg hi', if_neg hj'] at hij
    ext
    omega
  · intro i
    unfold wt sg
    split_ifs <;> norm_num
  · intro i
    unfold wt sg
    split_ifs <;> simp
  · intro i
    unfold wt pr
    by_cases h : ε i.rev = ε i
    · simp [h]
    · have h' : ¬ε i = ε i.rev := fun e => h e.symm
      simp [h, h']
  · intro i j hi hj
    have hi' := ht_eq_zero.mp hi
    have hj' := ht_eq_zero.mp hj
    have key : ∀ a b : Fin n, ε a.rev = ε a → ε b.rev = ε b → ε a = false → ε b = true → False := by
      intro a b ha hb h1 h2
      have t1 := lt_of_sign hε (ha.trans h1) h2
      have t2 := lt_of_sign hε h1 (hb.trans h2)
      rw [rev_cast] at t1 t2
      linarith
    have he : ε i = ε j := by
      cases h1 : ε i <;> cases h2 : ε j
      · rfl
      · exact (key i j hi' hj' h1 h2).elim
      · exact (key j i hj' hi' h2 h1).elim
      · rfl
    unfold wt sg
    rw [if_pos hi', if_pos hj', he]

theorem pr_eq_iff {ε : Fin n → Bool} {i : Fin n} : pr ε i = i ↔ ε i.rev = ε i := by
  unfold pr
  by_cases h : ε i.rev = ε i
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun e => (h (by rw [e])).elim, fun e => (h e).elim⟩

theorem dec_of_monotone {ε : Fin n → Bool} (hε : Monotone ε) : Dec (Jm ε) := by
  classical
  have hA := adapted hε
  have hp : ∀ i, pr ε (pr ε i) = i := pr_pr ε
  have hqq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hqs : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hsg2 : ∀ i, sg ε i * sg ε i = 1 := fun i => by unfold sg; split_ifs <;> norm_num
  have hsgs : ∀ i, star (sg ε i) = sg ε i := fun i => by unfold sg; split_ifs <;> simp
  have hnf : ∀ i, ¬ε i.rev = ε i →
      pr ε i = i.rev ∧ ¬ε (pr ε i).rev = ε (pr ε i) ∧ sg ε (pr ε i) = -sg ε i := by
    intro i h
    have hpi : pr ε i = i.rev := by unfold pr; rw [if_neg h]
    refine ⟨hpi, ?_, ?_⟩
    · rw [hpi, Fin.rev_rev]
      exact fun e => h e.symm
    · rw [hpi]
      unfold sg
      cases hx : ε i <;> cases hy : ε i.rev <;> simp_all
  generalize hq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = q at hqq hqs
  let α : Fin n → ℂ := fun i => if ε i.rev = ε i then 1 else q
  let β : Fin n → ℂ := fun i => if ε i.rev = ε i then 0 else sg ε i * q
  have hαs : ∀ i, star (α i) = α i := fun i => by simp only [α]; split_ifs <;> simp [hqs]
  have hβs : ∀ i, star (β i) = β i := fun i => by simp only [β]; split_ifs <;> simp [hqs, hsgs]
  have hVt : (dp (pr ε) α β).conjTranspose = dp (pr ε) α (fun i => β (pr ε i)) := by
    rw [dp_conjTranspose hp]
    simp only [hαs, hβs]
  have hJ : Jm ε = dp (pr ε) (sg ε) 0 := by
    rw [dp_diagonal]
    rfl
  apply Dec.of_conj (V := dp (pr ε) α β)
  · rw [hVt, dp_mul_dp hp, ← Matrix.diagonal_one, ← dp_diagonal (pr ε)]
    apply dp_congr
    · intro i hi
      have h := pr_eq_iff.mp hi
      simp [α, β, h, hi]
    · intro i hi
      have h : ¬ε i.rev = ε i := fun e => hi (pr_eq_iff.mpr e)
      obtain ⟨hpi, hpp, hs⟩ := hnf i h
      simp only [α, β, h, hpp, ↓reduceIte, hs, Pi.zero_apply]
      constructor
      · linear_combination (1 + sg ε i * sg ε i) * hqq + (1 / 2 : ℂ) * hsg2 i
      · ring
  · have key : (dp (pr ε) α β).conjTranspose * Jm ε * dp (pr ε) α β = dp (pr ε) 0 (wt ε) := by
      rw [hVt, hJ, dp_mul_dp hp, dp_mul_dp hp]
      apply dp_congr
      · intro i hi
        have h := pr_eq_iff.mp hi
        simp [α, β, h, hi, wt]
      · intro i hi
        have h : ¬ε i.rev = ε i := fun e => hi (pr_eq_iff.mpr e)
        obtain ⟨hpi, hpp, hs⟩ := hnf i h
        simp only [α, β, wt, h, hpp, ↓reduceIte, hs, Pi.zero_apply]
        constructor
        · linear_combination (-(sg ε i) * q * q) * hsg2 i
        · linear_combination (2 * sg ε i * sg ε i) * hqq + hsg2 i
    rw [key]
    exact hA.dec

theorem dec_Jm (ε : Fin n → Bool) : Dec (Jm ε) := by
  classical
  let σ := Tuple.sort ε
  have hmono : Monotone (ε ∘ σ) := Tuple.monotone_sort ε
  let V : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id σ
  have hV : ∀ H : Matrix (Fin n) (Fin n) ℂ, V.conjTranspose * H * V = H.submatrix σ σ := by
    intro H
    ext a b
    simp [V, Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  apply Dec.of_conj (V := V)
  · have h1 := hV 1
    rw [Matrix.mul_one] at h1
    rw [h1]
    exact Matrix.submatrix_one_equiv σ
  · rw [hV]
    have h2 : (Jm ε).submatrix σ σ = Jm (ε ∘ σ) := by
      unfold Jm
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [h2]
    exact dec_of_monotone hmono

end CholeskyDecomposition

theorem iwasawa_decomposition_unitary_group : IwaAll := by
  intro n ε
  obtain ⟨U, hU, h⟩ := CholeskyDecomposition.dec_Jm ε
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨k, hk, s, hkJ, hsJ, rfl, htri⟩ := h g hg
  refine ⟨k, ⟨hk, ?_⟩, s, hsJ, rfl, htri⟩
  have hk1 : k * k.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hk
  calc k * Jm ε = k * (k.conjTranspose * Jm ε * k) := by rw [hkJ]
    _ = k * k.conjTranspose * Jm ε * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * k := by rw [hk1, Matrix.one_mul]

end CompanionTheory.D.gk.admitted
