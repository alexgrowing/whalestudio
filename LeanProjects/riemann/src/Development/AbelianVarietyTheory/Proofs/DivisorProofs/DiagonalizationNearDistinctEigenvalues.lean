import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnMinorNormInequalityStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.ConstLat.EigenMinor

variable {K : Type} [Field K] (w : AbsoluteValue K ℝ)

theorem supN_zero' {n : ℕ} : supN w (0 : Fin n → K) = 0 :=
  le_antisymm (supN_le w le_rfl fun i => by simp) (supN_nonneg w _)

theorem eq_zero_of_supN_le {n : ℕ} {x : Fin n → K} (h : supN w x ≤ 0) : x = 0 := by
  funext i
  have := (le_supN w x i).trans h
  exact w.eq_zero.1 (le_antisymm this (w.nonneg _))

theorem supN_smul' {n : ℕ} (a : K) (x : Fin n → K) : supN w (a • x) = w a * supN w x := by
  unfold supN
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Real.mul_iSup_of_nonneg (w.nonneg a)]

theorem supN_neg' {n : ℕ} (y : Fin n → K) : supN w (-y) = supN w y := by
  unfold supN
  congr 1
  funext i
  exact w.map_neg (y i)

theorem exists_eq_supN {n : ℕ} {x : Fin n → K} (h : 0 < supN w x) : ∃ i, w (x i) = supN w x := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exfalso
    unfold supN at h
    rw [Real.iSup_of_isEmpty] at h
    exact lt_irrefl _ h
  · exact exists_eq_ciSup_of_finite (f := fun i => w (x i))

variable {w}

theorem sum_le_of_nonarch (hw : IsNonarchimedean w) {α : Type} (s : Finset α) (a : α → K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ σ ∈ s, w (a σ) ≤ c) : w (∑ σ ∈ s, a σ) ≤ c := by
  revert h
  refine Finset.induction_on s (fun _ => by simpa using hc) ?_
  intro x s hx ih h
  rw [Finset.sum_insert hx]
  exact (hw _ _).trans (max_le (h x (Finset.mem_insert_self _ _))
    (ih fun σ hσ => h σ (Finset.mem_insert_of_mem hσ)))

theorem sum_lt_of_nonarch (hw : IsNonarchimedean w) {α : Type} (s : Finset α) (a : α → K) {c : ℝ} (hc : 0 < c)
    (h : ∀ σ ∈ s, w (a σ) < c) : w (∑ σ ∈ s, a σ) < c := by
  revert h
  refine Finset.induction_on s (fun _ => by simpa using hc) ?_
  intro x s hx ih h
  rw [Finset.sum_insert hx]
  exact (hw _ _).trans_lt (max_lt (h x (Finset.mem_insert_self _ _))
    (ih fun σ hσ => h σ (Finset.mem_insert_of_mem hσ)))

theorem supN_mulVec_le (hw : IsNonarchimedean w) {n m : ℕ} (M : Matrix (Fin n) (Fin m) K) {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ i j, w (M i j) ≤ c) (v : Fin m → K) : supN w (M.mulVec v) ≤ c * supN w v := by
  apply supN_le w (mul_nonneg hc (supN_nonneg w v))
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply sum_le_of_nonarch hw _ _ (mul_nonneg hc (supN_nonneg w v))
  intro j _
  rw [map_mul]
  exact mul_le_mul (hM i j) (le_supN w v j) (w.nonneg _) hc

theorem supN_add_le' (hw : IsNonarchimedean w) {n : ℕ} (x y : Fin n → K) :
    supN w (x + y) ≤ max (supN w x) (supN w y) :=
  supN_le w (le_max_of_le_left (supN_nonneg w x)) fun i =>
    (hw (x i) (y i)).trans (max_le_max (le_supN w x i) (le_supN w y i))

theorem supN_sub_of_lt (hw : IsNonarchimedean w) {n : ℕ} (x y : Fin n → K) (h : supN w y < supN w x) :
    supN w (x - y) = supN w x := by
  apply le_antisymm
  · rw [sub_eq_add_neg]
    refine (supN_add_le' hw x (-y)).trans ?_
    rw [supN_neg']
    exact max_le le_rfl h.le
  · have h2 := supN_add_le' hw (x - y) y
    rw [sub_add_cancel] at h2
    rcases le_max_iff.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 (not_le.2 h)

end GlobalTheory.ConstLat.EigenMinor

namespace GlobalTheory.ConstLat.EigenMinor

variable {K : Type} [Field K] {w : AbsoluteValue K ℝ}

theorem approx_kind (hw : IsNonarchimedean w) {N g : ℕ} {ι : Type} (H : Matrix (Fin N) (Fin g) K)
    (R : Matrix (Fin N) (Fin N) K) (β : Fin g → ι) (χ : ι → K) (ε : ℝ)
    (happ : ∀ u : Fin g → K, supN w (H.mulVec u) ≤ 1 →
      supN w (R.mulVec (H.mulVec u) - H.mulVec fun l => χ (β l) * u l) ≤ ε)
    (τ : ι) (u : Fin g → K) (hu : ∀ l, β l ≠ τ → u l = 0) :
    supN w (R.mulVec (H.mulVec u) - χ τ • H.mulVec u) ≤ ε * supN w (H.mulVec u) := by
  have hk : ∀ v : Fin g → K, (∀ l, β l ≠ τ → v l = 0) → (fun l => χ (β l) * v l) = χ τ • v := by
    intro v hv
    funext l
    by_cases h : β l = τ
    · simp [h]
    · simp [hv l h]
  have key : ∀ v : Fin g → K, (∀ l, β l ≠ τ → v l = 0) → supN w (H.mulVec v) ≤ 1 →
      supN w (R.mulVec (H.mulVec v) - χ τ • H.mulVec v) ≤ ε := by
    intro v hv h1
    have := happ v h1
    rwa [hk v hv, Matrix.mulVec_smul] at this
  by_cases hs : supN w (H.mulVec u) ≤ 0
  · have h0 := eq_zero_of_supN_le w hs
    rw [h0, Matrix.mulVec_zero, smul_zero, sub_zero, supN_zero', mul_zero]
  · push_neg at hs
    obtain ⟨k, hk'⟩ := exists_eq_supN w hs
    have hwc : 0 < w (H.mulVec u k) := hk' ▸ hs
    have hc0 : H.mulVec u k ≠ 0 := fun h => by rw [h, map_zero] at hwc; exact lt_irrefl _ hwc
    have hv : ∀ l, β l ≠ τ → ((H.mulVec u k)⁻¹ • u) l = 0 := by
      intro l hl
      simp [hu l hl]
    have h1 : supN w (H.mulVec ((H.mulVec u k)⁻¹ • u)) ≤ 1 := by
      rw [Matrix.mulVec_smul, supN_smul', map_inv₀, ← hk', inv_mul_cancel₀ hwc.ne']
    have h2 := key _ hv h1
    have e : R.mulVec (H.mulVec ((H.mulVec u k)⁻¹ • u)) - χ τ • H.mulVec ((H.mulVec u k)⁻¹ • u) =
        (H.mulVec u k)⁻¹ • (R.mulVec (H.mulVec u) - χ τ • H.mulVec u) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub, smul_comm (χ τ) (H.mulVec u k)⁻¹]
    rw [e, supN_smul', map_inv₀, inv_mul_le_iff₀ hwc] at h2
    rw [← hk']
    linarith

theorem core (hw : IsNonarchimedean w) {N g : ℕ} {ι : Type} (H : Matrix (Fin N) (Fin g) K)
    (P Q R : Matrix (Fin N) (Fin N) K) (b : Fin N → ι) (β : Fin g → ι) (χ : ι → K) (lam : ι → ℝ) (η ε : ℝ)
    (hη : 0 < η) (hε : ε < η ^ 3) (hPQ : P * Q = 1) (hb : ∀ i j, w (P i j) ≤ η⁻¹ ∧ w (Q i j) ≤ η⁻¹)
    (hD : P * R * Q = Matrix.diagonal (fun r => χ (b r))) (hsep : ∀ σ τ, σ ≠ τ → η ≤ w (χ σ - χ τ))
    (hlam : ∀ (τ : ι) (y : Fin N → K), (∀ r, b r ≠ τ → y r = 0) → supN w y = lam τ * supN w (Q.mulVec y))
    (happ : ∀ u : Fin g → K, supN w (H.mulVec u) ≤ 1 →
      supN w (R.mulVec (H.mulVec u) - H.mulVec fun l => χ (β l) * u l) ≤ ε)
    (τ : ι) (u : Fin g → K) (hu : ∀ l, β l ≠ τ → u l = 0) :
    (∀ r, b r ≠ τ → w ((P * H).mulVec u r) ≤ η⁻¹ ^ 2 * ε * supN w (H.mulVec u)) ∧
    supN w (fun r => if b r = τ then (P * H).mulVec u r else 0) = lam τ * supN w (H.mulVec u) ∧
    η * supN w (H.mulVec u) ≤ supN w (fun r => if b r = τ then (P * H).mulVec u r else 0) := by
  have hε0 : 0 ≤ ε := by
    have h0 := happ 0 (by rw [Matrix.mulVec_zero, supN_zero']; norm_num)
    have e0 : (R.mulVec (H.mulVec 0) - H.mulVec fun l => χ (β l) * (0 : Fin g → K) l) = 0 := by
      rw [show (fun l => χ (β l) * (0 : Fin g → K) l) = 0 from funext fun l => by simp]
      simp
    rwa [e0, supN_zero'] at h0
  have hyx : (P * H).mulVec u = P.mulVec (H.mulVec u) := (Matrix.mulVec_mulVec u P H).symm
  have hQP : Q * P = 1 := mul_eq_one_comm.1 hPQ
  have hPR : P * R = Matrix.diagonal (fun r => χ (b r)) * P := by
    rw [← hD, Matrix.mul_assoc (P * R) Q P, hQP, Matrix.mul_one]
  have hηi : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hbound : ∀ (M : Matrix (Fin N) (Fin N) K), (∀ i j, w (M i j) ≤ η⁻¹) → ∀ v,
      supN w (M.mulVec v) ≤ η⁻¹ * supN w v :=
    fun M hM v => supN_mulVec_le hw M hηi hM v
  have c1 : ∀ r, b r ≠ τ → w ((P * H).mulVec u r) ≤ η⁻¹ ^ 2 * ε * supN w (H.mulVec u) := by
    intro r hr
    have ha := approx_kind hw H R β χ ε happ τ u hu
    have e : P.mulVec (R.mulVec (H.mulVec u) - χ τ • H.mulVec u) r = (χ (b r) - χ τ) * (P * H).mulVec u r := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPR, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, ← hyx]
      simp [Matrix.mulVec_diagonal, sub_mul]
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have h1 : w (P.mulVec (R.mulVec (H.mulVec u) - χ τ • H.mulVec u) r) ≤ η⁻¹ * (ε * supN w (H.mulVec u)) :=
      (le_supN w _ r).trans ((hbound P (fun i j => (hb i j).1) _).trans (mul_le_mul_of_nonneg_left ha hηi))
    rw [e, map_mul] at h1
    have h2 : η * w ((P * H).mulVec u r) ≤ η⁻¹ * (ε * supN w (H.mulVec u)) :=
      (mul_le_mul_of_nonneg_right (hsep _ _ hr) (w.nonneg _)).trans h1
    calc w ((P * H).mulVec u r) = η⁻¹ * (η * w ((P * H).mulVec u r)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
      _ ≤ η⁻¹ * (η⁻¹ * (ε * supN w (H.mulVec u))) := mul_le_mul_of_nonneg_left h2 hηi
      _ = η⁻¹ ^ 2 * ε * supN w (H.mulVec u) := by ring
  refine ⟨c1, ?_⟩
  by_cases hs : supN w (H.mulVec u) ≤ 0
  · have hx0 : H.mulVec u = 0 := eq_zero_of_supN_le w hs
    have hz : (fun r => if b r = τ then (P * H).mulVec u r else 0) = 0 := by
      funext r
      simp [hyx, hx0]
    rw [hz, supN_zero', hx0, supN_zero']
    simp
  · push_neg at hs
    set x := H.mulVec u with hx
    set y := (P * H).mulVec u with hy
    set z : Fin N → K := fun r => if b r = τ then y r else 0 with hz
    have hz' : ∀ r, b r ≠ τ → z r = 0 := fun r hr => by simp [hz, hr]
    have hK : 0 ≤ η⁻¹ ^ 2 * ε * supN w x := mul_nonneg (mul_nonneg (by positivity) hε0) hs.le
    have hyz : supN w (y - z) ≤ η⁻¹ ^ 2 * ε * supN w x := by
      apply supN_le w hK
      intro r
      by_cases hr : b r = τ
      · have : (y - z) r = 0 := by simp [hz, hr]
        rw [this, map_zero]
        exact hK
      · have : (y - z) r = y r := by simp [hz, hr]
        rw [this]
        exact c1 r hr
    have hQy : Q.mulVec y = x := by
      rw [hyx, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have hQz : Q.mulVec z = x - Q.mulVec (y - z) := by
      rw [Matrix.mulVec_sub, hQy]
      abel
    have hsmall : supN w (Q.mulVec (y - z)) < supN w x := by
      calc supN w (Q.mulVec (y - z)) ≤ η⁻¹ * supN w (y - z) := hbound Q (fun i j => (hb i j).2) _
        _ ≤ η⁻¹ * (η⁻¹ ^ 2 * ε * supN w x) := mul_le_mul_of_nonneg_left hyz hηi
        _ = (ε / η ^ 3) * supN w x := by rw [div_eq_mul_inv]; ring
        _ < 1 * supN w x := by
          apply mul_lt_mul_of_pos_right _ hs
          exact (div_lt_one (by positivity)).2 hε
        _ = supN w x := one_mul _
    have hQzx : supN w (Q.mulVec z) = supN w x := by
      rw [hQz]
      exact supN_sub_of_lt hw _ _ hsmall
    have hzl := hlam τ z hz'
    rw [hQzx] at hzl
    refine ⟨hzl, ?_⟩
    have h5 := hbound Q (fun i j => (hb i j).2) z
    rw [hQzx] at h5
    calc η * supN w x ≤ η * (η⁻¹ * supN w z) := mul_le_mul_of_nonneg_left h5 hη.le
      _ = supN w z := by rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]

end GlobalTheory.ConstLat.EigenMinor

namespace GlobalTheory.ConstLat.EigenMinor

variable {K : Type} [Field K] {w : AbsoluteValue K ℝ}

section Kinds

variable (hw : IsNonarchimedean w) {N g : ℕ} {ι : Type} (H : Matrix (Fin N) (Fin g) K)
    (P Q R : Matrix (Fin N) (Fin N) K) (b : Fin N → ι) (β : Fin g → ι) (χ : ι → K) (lam : ι → ℝ) (η ε : ℝ)
    (hη : 0 < η) (hε : ε < η ^ 3) (hPQ : P * Q = 1) (hb : ∀ i j, w (P i j) ≤ η⁻¹ ∧ w (Q i j) ≤ η⁻¹)
    (hD : P * R * Q = Matrix.diagonal (fun r => χ (b r))) (hsep : ∀ σ τ, σ ≠ τ → η ≤ w (χ σ - χ τ))
    (hlam : ∀ (τ : ι) (y : Fin N → K), (∀ r, b r ≠ τ → y r = 0) → supN w y = lam τ * supN w (Q.mulVec y))
    (happ : ∀ u : Fin g → K, supN w (H.mulVec u) ≤ 1 →
      supN w (R.mulVec (H.mulVec u) - H.mulVec fun l => χ (β l) * u l) ≤ ε)
include hw hη hε hPQ hb hD hsep hlam happ

theorem eq_kind (τ : ι) (u : Fin g → K) (hu : ∀ l, β l ≠ τ → u l = 0) :
    supN w ((P * H).mulVec u) = lam τ * supN w (H.mulVec u) := by
  obtain ⟨c1, c2, c3⟩ := core hw H P Q R b β χ lam η ε hη hε hPQ hb hD hsep hlam happ τ u hu
  rw [← c2]
  apply le_antisymm
  · apply supN_le w (supN_nonneg w _)
    intro r
    by_cases hr : b r = τ
    · have := le_supN w (fun r => if b r = τ then (P * H).mulVec u r else 0) r
      simpa [hr] using this
    · refine (c1 r hr).trans (le_trans ?_ c3)
      apply mul_le_mul_of_nonneg_right _ (supN_nonneg w _)
      have e : η⁻¹ ^ 2 * ε = ε / η ^ 2 := by rw [div_eq_mul_inv, inv_pow]; ring
      rw [e, div_le_iff₀ (by positivity)]
      have : η ^ 3 = η * η ^ 2 := by ring
      linarith
  · apply supN_le w (supN_nonneg w _)
    intro r
    by_cases hr : b r = τ
    · simpa [hr] using le_supN w ((P * H).mulVec u) r
    · simp only [hr, if_false, map_zero]
      exact supN_nonneg w _

theorem ge_kind (u : Fin g → K) (τ : ι) :
    lam τ * supN w (H.mulVec (fun l => if β l = τ then u l else 0)) ≤ supN w ((P * H).mulVec u) := by
  let S : Finset ι := insert τ (Finset.univ.image β)
  let uk : ι → Fin g → K := fun σ l => if β l = σ then u l else 0
  let f : ι → ℝ := fun σ => supN w (fun r => if b r = σ then (P * H).mulVec (uk σ) r else 0)
  have hcore := fun σ => core hw H P Q R b β χ lam η ε hη hε hPQ hb hD hsep hlam happ σ (uk σ)
    (fun l hl => by simp [uk, hl])
  obtain ⟨σ0, hσ0, hmax⟩ := S.exists_max_image f ⟨τ, Finset.mem_insert_self _ _⟩
  show lam τ * supN w (H.mulVec (uk τ)) ≤ _
  rw [← (hcore τ).2.1]
  refine (hmax τ (Finset.mem_insert_self _ _)).trans ?_
  by_cases hf : f σ0 ≤ 0
  · exact hf.trans (supN_nonneg w _)
  push_neg at hf
  obtain ⟨r0, hr0⟩ := exists_eq_supN w hf
  have hb0 : b r0 = σ0 := by
    by_contra h
    simp only [h, if_false, map_zero] at hr0
    exact absurd hr0 hf.ne
  have hy0 : w ((P * H).mulVec (uk σ0) r0) = f σ0 := by simpa [hb0] using hr0
  have hdec : u = ∑ σ ∈ S, uk σ := by
    funext l
    rw [Finset.sum_apply]
    simp only [uk]
    rw [Finset.sum_ite_eq S (β l) (fun _ => u l)]
    simp [S]
  have hsum : (P * H).mulVec u r0 =
      (P * H).mulVec (uk σ0) r0 + ∑ σ ∈ S.erase σ0, (P * H).mulVec (uk σ) r0 := by
    conv_lhs => rw [hdec]
    rw [Matrix.mulVec_sum, Finset.sum_apply, ← Finset.add_sum_erase _ _ hσ0]
  have herr : w (∑ σ ∈ S.erase σ0, (P * H).mulVec (uk σ) r0) < f σ0 := by
    apply sum_lt_of_nonarch hw _ _ hf
    intro σ hσ
    have hne : b r0 ≠ σ := by rw [hb0]; exact (Finset.ne_of_mem_erase hσ).symm
    have h1 := (hcore σ).1 r0 hne
    have h3 := (hcore σ).2.2
    have h4 := hmax σ (Finset.mem_of_mem_erase hσ)
    have hs0 : 0 ≤ supN w (H.mulVec (uk σ)) := supN_nonneg w _
    rcases hs0.eq_or_lt with h | h
    · rw [← h, mul_zero] at h1
      linarith
    · have : η⁻¹ ^ 2 * ε * supN w (H.mulVec (uk σ)) < η * supN w (H.mulVec (uk σ)) := by
        apply mul_lt_mul_of_pos_right _ h
        have e : η⁻¹ ^ 2 * ε = ε / η ^ 2 := by rw [div_eq_mul_inv, inv_pow]; ring
        rw [e, div_lt_iff₀ (by positivity)]
        have : η ^ 3 = η * η ^ 2 := by ring
        linarith
      linarith
  have key : f σ0 ≤ w ((P * H).mulVec u r0) := by
    rw [hsum, ← hy0]
    have h6 := hw ((P * H).mulVec (uk σ0) r0 + ∑ σ ∈ S.erase σ0, (P * H).mulVec (uk σ) r0)
      (-(∑ σ ∈ S.erase σ0, (P * H).mulVec (uk σ) r0))
    rw [add_neg_cancel_right, w.map_neg] at h6
    rcases le_max_iff.1 h6 with h | h
    · exact h
    · rw [hy0] at h ⊢
      exact absurd h (not_le.2 herr)
  exact key.trans (le_supN w _ r0)

end Kinds

end GlobalTheory.ConstLat.EigenMinor

namespace GlobalTheory.ConstLat.EigenMinor

theorem graded_minor_log_eigen : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ {N g : ℕ} {ι : Type}
    (H : Matrix (Fin N) (Fin g) K) (P Q R : Matrix (Fin N) (Fin N) K) (b : Fin N → ι) (β : Fin g → ι) (χ : ι → K)
    (lam : ι → ℝ) (η ε : ℝ), 0 < η → η ≤ 1 → ε < η ^ 3 → P * Q = 1 → (∀ i j, w (P i j) ≤ η⁻¹ ∧ w (Q i j) ≤ η⁻¹) →
    P * R * Q = Matrix.diagonal (fun r => χ (b r)) → (∀ σ τ, σ ≠ τ → η ≤ w (χ σ - χ τ)) →
    (∀ (τ : ι) (y : Fin N → K), (∀ r, b r ≠ τ → y r = 0) → supN w y = lam τ * supN w (Q.mulVec y)) →
    (∀ u : Fin g → K, supN w (H.mulVec u) ≤ 1 →
      supN w (R.mulVec (H.mulVec u) - H.mulVec fun l => χ (β l) * u l) ≤ ε) →
    0 < colMinor w H Finset.univ →
    0 < colMinor w (P * H) Finset.univ ∧ ∀ i : Fin g, 0 < lam (β i) ∧
      Real.log (colMinor w (P * H) (Finset.Iic i)) - Real.log (colMinor w (P * H) (Finset.Iio i)) =
        Real.log (colMinor w H (blkLe β i)) - Real.log (colMinor w H (blkLt β i)) + Real.log (lam (β i)) := by
  intro K _ w hw N g ι H P Q R b β χ lam η ε hη _ hε hPQ hb hD hsep hlam happ hH
  have hinjH : Function.Injective H.mulVec := (GlobalTheory.T.column_minor_norm_inequality w hw H).1.1 hH
  have hQP : Q * P = 1 := mul_eq_one_comm.1 hPQ
  have hinjPH : Function.Injective (P * H).mulVec := by
    intro u v huv
    apply hinjH
    have h2 := congrArg Q.mulVec huv
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at h2
    exact h2
  refine ⟨(GlobalTheory.T.column_minor_norm_inequality w hw (P * H)).1.2 hinjPH, fun i => ?_⟩
  obtain ⟨hposH, hminH⟩ := (GlobalTheory.T.column_minor_norm_inequality w hw H).2 hinjH
  obtain ⟨hposPH, hminPH⟩ := (GlobalTheory.T.column_minor_norm_inequality w hw (P * H)).2 hinjPH
  have hlampos : 0 < lam (β i) := by
    have hu : ∀ l, β l ≠ β i → (Pi.single i (1 : K) : Fin g → K) l = 0 := by
      intro l hl
      have : l ≠ i := by rintro rfl; exact hl rfl
      simp [Pi.single_apply, this]
    obtain ⟨_, c2, c3⟩ := core hw H P Q R b β χ lam η ε hη hε hPQ hb hD hsep hlam happ (β i) _ hu
    have hne : H.mulVec (Pi.single i (1 : K)) ≠ 0 := by
      intro h
      have h' := hinjH (h.trans (Matrix.mulVec_zero H).symm)
      have := congrFun h' i
      simp at this
    have hs : 0 < supN w (H.mulVec (Pi.single i (1 : K))) := by
      by_contra h
      push_neg at h
      exact hne (eq_zero_of_supN_le w h)
    rw [c2] at c3
    have := le_of_mul_le_mul_right c3 hs
    linarith
  have hiIio : i ∉ Finset.Iio i := by simp
  have hiblk : i ∉ blkLt β i := by simp [blkLt]
  have hIic : insert i (Finset.Iio i) = Finset.Iic i := Finset.Iio_insert i
  have hblk : insert i (blkLt β i) = blkLe β i := by
    ext l
    simp only [Finset.mem_insert, blkLt, blkLe, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨le_rfl, rfl⟩
      · exact ⟨h1.le, h2⟩
    · rintro ⟨h1, h2⟩
      rcases h1.lt_or_eq with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl h
  obtain ⟨hle1, u1, hu1i, hu1s, heq1⟩ := hminPH (Finset.Iio i) i hiIio
  obtain ⟨hle2, u2, hu2i, hu2s, heq2⟩ := hminH (blkLt β i) i hiblk
  rw [hIic] at hle1 heq1
  rw [hblk] at hle2 heq2

  have hup : supN w ((P * H).mulVec u1) ≤ lam (β i) * supN w (H.mulVec u2) := by
    have hv : ∀ l, l ∉ Finset.Iio i → l ≠ i → u2 l = 0 := by
      intro l hl hne
      apply hu2s l _ hne
      simp only [blkLt, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨h, _⟩
      exact hl (Finset.mem_Iio.2 h)
    have hk : ∀ l, β l ≠ β i → u2 l = 0 := by
      intro l hl
      have hne : l ≠ i := by rintro rfl; exact hl rfl
      apply hu2s l _ hne
      simp only [blkLt, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨_, h⟩
      exact hl h
    have h1 := hle1 u2 hu2i hv
    rw [heq1, eq_kind hw H P Q R b β χ lam η ε hη hε hPQ hb hD hsep hlam happ (β i) u2 hk] at h1
    exact le_of_mul_le_mul_left h1 (hposPH _)

  have hlow : lam (β i) * supN w (H.mulVec u2) ≤ supN w ((P * H).mulVec u1) := by
    have hv : ∀ l, l ∉ blkLt β i → l ≠ i → (fun l => if β l = β i then u1 l else 0) l = 0 := by
      intro l hl hne
      by_cases hβ : β l = β i
      · have hlt : ¬ l < i := fun h => hl (by simp [blkLt, h, hβ])
        simp only [hβ, if_true]
        exact hu1s l (by simpa using hlt) hne
      · simp [hβ]
    have h1 := hle2 _ (by simp [hu1i]) hv
    rw [heq2] at h1
    have h2 := le_of_mul_le_mul_left h1 (hposH _)
    exact (mul_le_mul_of_nonneg_left h2 hlampos.le).trans
      (ge_kind hw H P Q R b β χ lam η ε hη hε hPQ hb hD hsep hlam happ u1 (β i))
  have hab : supN w ((P * H).mulVec u1) = lam (β i) * supN w (H.mulVec u2) := le_antisymm hup hlow
  have ha : 0 < supN w ((P * H).mulVec u1) := by
    have := hposPH (Finset.Iic i)
    rw [heq1] at this
    exact pos_of_mul_pos_right this (hposPH _).le
  have hb2 : 0 < supN w (H.mulVec u2) := by
    have := hposH (blkLe β i)
    rw [heq2] at this
    exact pos_of_mul_pos_right this (hposH _).le
  refine ⟨hlampos, ?_⟩
  rw [heq1, heq2, Real.log_mul (hposPH _).ne' ha.ne', Real.log_mul (hposH _).ne' hb2.ne', hab,
    Real.log_mul hlampos.ne' hb2.ne']
  ring

end GlobalTheory.ConstLat.EigenMinor
