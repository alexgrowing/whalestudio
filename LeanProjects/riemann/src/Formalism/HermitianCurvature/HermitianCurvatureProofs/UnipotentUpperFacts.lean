import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace UnipotentUpperFacts

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector

section gen

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

lemma agree (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (A B : Matrix n n ℂ)
    (hV : A * V = B * V) (hU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → A *ᵥ x = B *ᵥ x) : A = B := by
  have hV' : ∀ y, A *ᵥ (V *ᵥ y) = B *ᵥ (V *ᵥ y) := by
    intro y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hV]
  have key : ∀ x, A *ᵥ x = B *ᵥ x := by
    intro x
    have hd := decomp H V hΓ x
    have ex : x = V *ᵥ (prj H V *ᵥ x) + (x - V *ᵥ (prj H V *ᵥ x)) := by abel
    rw [ex, Matrix.mulVec_add, Matrix.mulVec_add, hU _ hd, hV']
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

lemma conj_pow (γ X : Matrix n n ℂ) (hγ : IsUnit γ.det) (p : ℕ) : (γ⁻¹ * X * γ) ^ p = γ⁻¹ * X ^ p * γ := by
  induction p with
  | zero => simp [Matrix.nonsing_inv_mul _ hγ]
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]

lemma blk_pow {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix p p ℂ) (D : Matrix q q ℂ) (m : ℕ) :
    (Matrix.fromBlocks A 0 0 D) ^ m = Matrix.fromBlocks (A ^ m) 0 0 (D ^ m) := by
  induction m with
  | zero => simp [Matrix.fromBlocks_one]
  | succ m ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply, pow_succ, pow_succ]; simp

end gen

lemma ut_sub_pow {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : (u - 1) ^ m = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, Matrix.one_apply]
  rcases lt_or_eq_of_le hji with h | h
  · rw [hu.1 i j h, if_neg (fun e => by subst e; exact lt_irrefl _ h), sub_zero]
  · subst h; rw [hu.2, if_pos rfl, sub_self]

variable {k r : ℕ}

lemma N_upper {g : B.Mat k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hji : j ≤ i) :
    g i j = if i = j then 1 else 0 := by
  have hc := ((WeylGroupFacts.nset_iff g).mp hg).2
  by_cases hj : j.val ≤ r + k
  · exact hc i j hj (Or.inl hji)
  · push Not at hj
    have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
      apply Matrix.inv_eq_left_inv
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, WeylGroupFacts.hpk_sq]
    have hci := ((WeylGroupFacts.nset_iff _).mp (WeylGroupFacts.mem_n_inv hg)).2
    rw [hinv] at hci
    have hle : j.val ≤ i.val := hji
    have hsj := GBasic.sig_val k r j
    have hsi := GBasic.sig_val k r i
    rw [if_pos (Or.inr hj)] at hsj
    rw [if_pos (Or.inr (by omega))] at hsi
    have h := hci (GBasic.sig k r j) (GBasic.sig k r i) (by omega) (Or.inl (by omega))
    rw [Matrix.mul_assoc, Hpk_mul_apply, mul_Hpk_apply, Matrix.conjTranspose_apply, GBasic.sig_sig,
      GBasic.sig_sig] at h
    have hs1 : GBasic.sgn k r (GBasic.sig k r j) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    have hs2 : GBasic.sgn k r (GBasic.sig k r i) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    rw [hs1, hs2, one_mul, mul_one] at h
    have hiff : (GBasic.sig k r j = GBasic.sig k r i) ↔ (i = j) := by
      constructor
      · intro e; have := congrArg (GBasic.sig k r) e; rw [GBasic.sig_sig, GBasic.sig_sig] at this; exact this.symm
      · intro e; rw [e]
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : i = j
    · rw [if_pos (hiff.mpr e), if_pos e, star_one]
    · rw [if_neg (fun e' => e (hiff.mp e')), if_neg e, star_zero]

lemma N_unip {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, N_upper hg i j hji, Matrix.one_apply, sub_self]

end UnipotentUpperFacts

end Formalism.FourierDecayAlt.P
