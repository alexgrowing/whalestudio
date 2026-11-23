import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero

open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE

noncomputable section

namespace PI.OneCosetSharp.W.P2

def S (k₀ m t N p q : ℕ) : Prop := p = q ∨ Allow k₀ m t N p q

theorem allow_col_lt {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : p < k₀ + m - 1 := by
  unfold Allow at h
  split_ifs at h <;> omega

theorem S_trans {k₀ m t N p q s : ℕ} (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q s) : S k₀ m t N p s := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  by_cases hps : p = s
  · exact Or.inl hps
  right
  unfold Allow at h1 h2 ⊢
  generalize (p - (k₀ + m - 1)) / t = bp at *
  generalize (q - (k₀ + m - 1)) / t = bq at *
  generalize (s - (k₀ + m - 1)) / t = bs at *
  split_ifs at h1 h2 ⊢ <;> omega

def φ (k₀ m p : ℕ) : ℕ := if p < k₀ then m + p else if p < k₀ + (m / 2 - 1) then p - k₀ else p + 2 * m + k₀

theorem allow_lt_φ {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : φ k₀ m p < φ k₀ m q := by
  unfold Allow at h
  unfold φ
  split_ifs at h ⊢ <;> omega

theorem S_antisymm {k₀ m t N p q : ℕ} (hp : p < k₀ + m - 1) (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q p) : p = q := by
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  have hq := allow_col_lt hp h2
  have a := allow_lt_φ hq h1
  have b := allow_lt_φ hp h2
  omega

variable {k : Type} [Field k]

def alg (k₀ m t b : ℕ) : Submodule k (Matrix (Fin b) (Fin b) k) where
  carrier := {A | ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1}
  add_mem' := by
    intro A B hA hB p q h
    by_contra hs
    apply h
    simp only [Matrix.add_apply]
    rw [not_imp_comm.1 (hA p q) hs, not_imp_comm.1 (hB p q) hs, add_zero]
  zero_mem' := fun _ _ h => absurd rfl h
  smul_mem' := by
    intro a A hA p q h
    by_contra hs
    apply h
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [not_imp_comm.1 (hA p q) hs, mul_zero]

variable {k₀ m t b : ℕ}

theorem mem_alg {A : Matrix (Fin b) (Fin b) k} : A ∈ alg (k := k) k₀ m t b ↔ ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1 :=
  Iff.rfl

theorem alg_one : (1 : Matrix (Fin b) (Fin b) k) ∈ alg (k := k) k₀ m t b := by
  intro p q h
  left
  rw [Matrix.one_apply] at h
  split_ifs at h with hpq
  · exact congrArg Fin.val hpq
  · exact absurd rfl h

theorem alg_mul {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b) :
    A * B ∈ alg (k := k) k₀ m t b := by
  intro p q h
  rw [Matrix.mul_apply] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact S_trans (hA p s (left_ne_zero_of_mul hs)) (hB s q (right_ne_zero_of_mul hs))

theorem alg_inv {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hBA : B * A = 1) :
    B ∈ alg (k := k) k₀ m t b := by
  let f : alg (k := k) k₀ m t b →ₗ[k] alg (k := k) k₀ m t b :=
    (LinearMap.mulLeft k A).restrict (fun X hX => alg_mul hA hX)
  have hf : ∀ X : alg (k := k) k₀ m t b, (f X).1 = A * X.1 := fun X => rfl
  have hinj : Function.Injective f := by
    intro X Y hXY
    have h1 : A * X.1 = A * Y.1 := by rw [← hf, ← hf, hXY]
    apply Subtype.ext
    have h2 := congrArg (B * ·) h1
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using h2
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨1, alg_one⟩
  have hAX : A * X.1 = 1 := by rw [← hf, hX]
  have : B = X.1 := by
    calc B = B * (A * X.1) := by rw [hAX, Matrix.mul_one]
      _ = X.1 := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [this]
  exact X.2

theorem alg_diag {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b)
    (p : Fin b) (hp : p.1 < k₀ + m - 1) : (A * B) p p = A p p * B p p := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · intro s _ hs
    by_contra h
    exact hs (Fin.ext (S_antisymm hp (hA p s (left_ne_zero_of_mul h)) (hB s p (right_ne_zero_of_mul h)))).symm
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p q : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hq : q < n + c)
    (h : fIdx k₀ c n p = fIdx k₀ c n q) : p = q := by
  unfold fIdx at h
  split_ifs at h <;> omega

def fe (k₀ c n : ℕ) (hk : k₀ ≤ n) : Fin (n + c) ≃ Fin (n + c) :=
  Equiv.ofBijective (fun p => ⟨fIdx k₀ c n p.1, fIdx_lt hk p.2⟩)
    (Finite.injective_iff_bijective.1 fun p q h => Fin.ext (fIdx_inj hk p.2 q.2 (congrArg Fin.val h)))

def Pm {c n : ℕ} (k₀ : ℕ) (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Matrix (Fin (n + c)) (Fin (n + c)) k :=
  (LinearMap.toMatrix' κ.toLinearMap).submatrix (fe k₀ c n hk) (fe k₀ c n hk)

theorem ent_eq {c n : ℕ} (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (p q : Fin (n + c)) :
    ent k₀ c n c n κ.toLinearMap p.1 q.1 = Pm k₀ hk κ p q := by
  have e : eN k (n + c) (fIdx k₀ c n q.1) = Pi.single (fe k₀ c n hk q) (1 : k) := by
    funext j'
    simp only [eN, Pi.single_apply, fe, Equiv.ofBijective_apply, Fin.ext_iff]
  simp only [Pm, Matrix.submatrix_apply, LinearMap.toMatrix'_apply, ent, atN, dif_pos (fIdx_lt hk p.2), e]
  rfl

theorem Pm_mul {c n : ℕ} (hk : k₀ ≤ n) (κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Pm k₀ hk (κ₁ * κ₂) = Pm k₀ hk κ₁ * Pm k₀ hk κ₂ := by
  have e : (κ₁ * κ₂).toLinearMap = κ₁.toLinearMap ∘ₗ κ₂.toLinearMap := LinearMap.ext fun _ => rfl
  rw [Pm, Pm, Pm, e, LinearMap.toMatrix'_comp, Matrix.submatrix_mul_equiv]

theorem Pm_one {c n : ℕ} (hk : k₀ ≤ n) : Pm (k := k) (c := c) (n := n) k₀ hk 1 = 1 := by
  have e : (1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)).toLinearMap = LinearMap.id := LinearMap.ext fun _ => rfl
  rw [Pm, e, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv]

theorem injs_iff {c n : ℕ} (hk : k₀ ≤ n) (hr : k₀ + m - 1 ≤ n + c) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    InJS k₀ m t c n κ ↔ Pm k₀ hk κ ∈ alg (k := k) k₀ m t (n + c) ∧ ∀ p : Fin (n + c), p.1 < k₀ + m - 1 → Pm k₀ hk κ p p = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p q h => ?_, fun p hp => ?_⟩
    · by_cases hpq : p = q
      · exact Or.inl (congrArg Fin.val hpq)
      · right
        refine h2 p.1 q.1 p.2 q.2 (fun e => hpq (Fin.ext e)) ?_
        rwa [ent_eq hk]
    · rw [← ent_eq hk]
      exact h1 p.1 hp
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p q hp hq hpq h => ?_⟩
    · have := h2 ⟨p, by omega⟩ hp
      rwa [← ent_eq hk] at this
    · rw [show p = (⟨p, hp⟩ : Fin (n + c)).1 from rfl, show q = (⟨q, hq⟩ : Fin (n + c)).1 from rfl, ent_eq hk] at h
      rcases h1 _ _ h with h | h
      · exact absurd h hpq
      · exact h

theorem nums_le {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) : k₀ ≤ n ∧ k₀ + m - 1 ≤ n + c := by
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8⟩ := h
  generalize j * t = J at h8
  omega

end PI.OneCosetSharp.W.P2

namespace PI.OneCosetSharp.W

open P2 in
theorem patClosed : PatClosed := by
  intro k _ k₀ m t j n' c n hN κ₁ κ₂ h₁ h₂
  obtain ⟨hk, hr⟩ := nums_le hN
  rw [injs_iff hk hr] at h₁ h₂
  refine ⟨?_, ?_⟩
  · rw [injs_iff hk hr, Pm_mul]
    refine ⟨alg_mul h₁.1 h₂.1, fun p hp => ?_⟩
    rw [alg_diag h₁.1 h₂.1 p hp, h₁.2 p hp, h₂.2 p hp, mul_one]
  · have hBA : Pm k₀ hk κ₁⁻¹ * Pm k₀ hk κ₁ = 1 := by rw [← Pm_mul, inv_mul_cancel, Pm_one]
    have hB := alg_inv h₁.1 hBA
    rw [injs_iff hk hr]
    refine ⟨hB, fun p hp => ?_⟩
    have := congrFun (congrFun hBA p) p
    rw [alg_diag hB h₁.1 p hp, h₁.2 p hp, mul_one, Matrix.one_apply_eq] at this
    exact this

end PI.OneCosetSharp.W
