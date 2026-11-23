import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem toGQ_mul_pos' (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dif_pos hmm, dif_pos h, dif_pos h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem sl_trans_of_lev {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : X.K)
    (hf : Lev X M f) (t : ℕ) : X.sl (toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1]) f = f := by
  let γ : SL(2, ℤ) := ⟨!![1, ((t * M : ℕ) : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [γ]
  have e : toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1] = ofSL γ := Betti.toGQ_sl γ
  rw [e]; exact hf γ hγ

theorem Nq_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  intro Ω _ _ _ ε X M M' q f hq hdvd hcop hlev
  obtain ⟨e, rfl⟩ := hdvd
  have hqe : Nat.Coprime q e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e M) hcop
  set g : ℕ → X.K := fun i => X.sl (toGQ !![1, ((i : ℤ) * (M : ℤ)); 0, (q : ℤ)]) f with hg
  have step : ∀ j : ℕ, X.sl (toGQ !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)]) f = g (j * e % q) := by
    intro j
    have hm : !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)] =
        !![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] * !![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] := by
      have hd := Nat.mod_add_div (j * e) q
      generalize j * e % q = a at hd ⊢
      generalize j * e / q = b at hd ⊢
      have hdz : (a : ℤ) + (q : ℤ) * (b : ℤ) = (j : ℤ) * (e : ℤ) := by exact_mod_cast hd
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M : ℤ) * hdz.symm
    have h1 : (0 : ℤ) < (!![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]
    have h2 : (0 : ℤ) < (!![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]; exact_mod_cast hq
    rw [hm, toGQ_mul_pos' _ _ h1 h2, X.sl_mul, sl_trans_of_lev X M f hlev]
  have hinj : Set.InjOn (fun j => j * e % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' : a * e ≡ b * e [MOD q] := hab
    have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hqe) h'
    simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have himg : (Finset.range q).image (fun j => j * e % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨j, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  unfold Nq
  simp_rw [step]
  show ∏ j ∈ Finset.range q, g j = _
  rw [← Finset.prod_image (f := g) hinj, himg]

end GlobalTheory.KZ.ES
