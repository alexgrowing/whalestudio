import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend

open Matrix

namespace GlobalTheory.Amp.BlockFrame

theorem blockAnti_scaled_pairing : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  intro K _ j r hj w
  obtain ⟨τ, γ, t, ht⟩ := GlobalTheory.HL.BlockStab.exists_monomial (E := K) w.blocks
  rw [w.size] at ht

  have hγN : ∀ a, a < j → γ a < (Finset.range j).sup γ + 1 := fun a ha =>
    Nat.lt_succ_of_le (Finset.le_sup (f := γ) (Finset.mem_range.mpr ha))
  refine ⟨fun a => if (a : ℕ) < j then γ a else (Finset.range j).sup γ + 1, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    dsimp only
    split_ifs with h1 h2 h2
    · exact ((ht a h1).2.2.2 b h2).2.1 hab'
    · exact (hγN a h1).le
    · omega
    · exact le_rfl
  · intro a b hb
    have hb' : ¬ ((b : ℕ) < j) := by omega
    dsimp only
    rw [if_neg hb']
    by_cases ha : (a : ℕ) < j
    · rw [if_pos ha]
      exact ⟨fun h => absurd h (hγN a ha).ne, fun h => absurd h (by omega)⟩
    · rw [if_neg ha]
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  · intro σ sgn ρ hρ
    simp only [Fin.val_castLE, Fin.is_lt, if_true]

    have hent : ∀ a b : Fin j, w.mat b a = if (a : ℕ) = τ b then (t (γ b) : K) else 0 :=
      fun a b => ((ht b b.isLt).2.2.2 a a.isLt).2.2.2
    have key : ∀ a b : Fin j,
        (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * σ (w.mat b a * ((sgn a : ℤ) : K)) ≠ 0 →
          (a : ℕ) = τ b := by
      intro a b h
      by_contra hne
      apply h
      rw [hent a b, if_neg hne, zero_mul, map_zero, mul_zero]
    have hs : ∀ a : Fin j, ‖σ ((sgn a : ℤ) : K)‖ = 1 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]
    have hsK : ∀ a : Fin j, ((sgn a : ℤ) : K) ≠ 0 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]

    have hZ : (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) =
        Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) *
          (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ *
          Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
        Matrix.transpose_apply, Complex.ofReal_mul, map_mul]
      ring
    have hd : ∀ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 := fun a =>
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hρ.ne'))
    unfold GlobalTheory.Amp.BlockAnti
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact ((ht a a.isLt).2.2.2 b b.isLt).2.1 hab
    · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
        show ((Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ).det =
          σ (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).det from
          (RingHom.map_det σ _).symm,
        Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
      have hP : ∏ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun a _ => hd a
      refine mul_ne_zero (mul_ne_zero hP ?_) hP
      exact (map_ne_zero σ).mpr (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => hsK a)
        (GlobalTheory.SgLoc.PtAlg.isUnit_det w).ne_zero)
    · intro a b h
      have e := key a b h
      show γ a = γ b
      rw [e]
      exact (ht b b.isLt).2.2.1
    · intro a b a' b' h1 h2 hγ
      have hγ' : γ a = γ a' := hγ
      have e1 := key a b h1
      have e2 := key a' b' h2
      have hb : (b : ℕ) = τ a := by rw [e1, (ht b b.isLt).2.1]
      have hb' : (b' : ℕ) = τ a' := by rw [e2, (ht b' b'.isLt).2.1]
      have hsum : (a : ℕ) + τ a = a' + τ a' := ((ht a a.isLt).2.2.2 a' a'.isLt).2.2.1 hγ'
      refine ⟨?_, ?_, ?_⟩
      · have hγb : γ b = γ a := by rw [hb]; exact (ht a a.isLt).2.2.1
        have hγb' : γ b' = γ a := by rw [hb', hγ']; exact (ht a' a'.isLt).2.2.1
        have hw1 : w.mat b a = (t (γ a) : K) := by rw [hent a b, if_pos e1, hγb]
        have hw2 : w.mat b' a' = (t (γ a) : K) := by rw [hent a' b', if_pos e2, hγb']
        have ha := a.isLt
        have hb2 := b.isLt
        have ha' := a'.isLt
        have hb2' := b'.isLt
        have hexp : (r - b.val) + (r - a.val) = (r - b'.val) + (r - a'.val) := by omega
        have hc : ((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) =
            (ρ ^ (r - b'.val))⁻¹ * (ρ ^ (r - a'.val))⁻¹ := by
          rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add, hexp]
        simp only [Matrix.of_apply]
        rw [hw1, hw2, hc, norm_mul, norm_mul, map_mul, map_mul, norm_mul, norm_mul, hs a, hs a']
      · intro haa
        subst haa
        exact Fin.ext (hb.trans hb'.symm)
      · intro hlt
        have hlt' : (a : ℕ) < a' := hlt
        exact Fin.lt_def.mpr (by omega)

end GlobalTheory.Amp.BlockFrame
