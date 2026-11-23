import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf

noncomputable section
open Classical Polynomial

namespace Formalism.L2.PairingIndexBounds.Eq.J

section Abstract

variable {E : Type} [Field E] [CharZero E] [StarRing E]

theorem one_add_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) + t * s ≠ 0 := by
  intro h
  have h2 : (1 : E) - t * s = 0 := by
    have := congrArg star h
    simpa [hs, sub_eq_add_neg] using this
  have h3 : (2 : E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

theorem one_sub_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) - t * s ≠ 0 := by
  have := one_add_ne (-s) (by rw [star_neg, hs]) t
  simpa [sub_eq_add_neg] using this

def cay (s : E) (t : ℕ) : E := (1 + t * s) / (1 - t * s)

theorem cay_norm (s : E) (hs : star s = -s) (t : ℕ) : star (cay s t) * cay s t = 1 := by
  have h1 := one_add_ne s hs t
  have h2 := one_sub_ne s hs t
  have : star (cay s t) = (1 - t * s) / (1 + t * s) := by
    unfold cay
    rw [star_div₀]
    simp [hs, sub_eq_add_neg]
  rw [this]
  unfold cay
  field_simp

theorem cay_inj (s : E) (hs : star s = -s) (hs0 : s ≠ 0) : Function.Injective (cay s) := by
  intro t u h
  unfold cay at h
  rw [div_eq_div_iff (one_sub_ne s hs t) (one_sub_ne s hs u)] at h
  have h2 : (2 : E) * s * ((t : E) - u) = 0 := by linear_combination h
  have h3 : (t : E) - u = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact absurd h4 (mul_ne_zero two_ne_zero hs0)
    · exact h4
  exact_mod_cast sub_eq_zero.mp h3

theorem exists_norm_one (s : E) (hs : star s = -s) (hs0 : s ≠ 0) (p : E[X]) (hp : p ≠ 0) :
    ∃ z : E, star z * z = 1 ∧ z ≠ 1 ∧ p.eval z ≠ 0 := by
  have hinf := Set.infinite_range_of_injective (cay_inj s hs hs0)
  obtain ⟨z, ⟨t, rfl⟩, hz⟩ := hinf.exists_notMem_finset (p.roots.toFinset ∪ {1})
  rw [Finset.mem_union, not_or, Multiset.mem_toFinset, Finset.mem_singleton, mem_roots hp] at hz
  exact ⟨_, cay_norm s hs t, hz.2, hz.1⟩

theorem eval_charpolyRev' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite]
  exact mul_comm _ _

theorem split_unitary (s : E) (hs : star s = -s) (hs0 : s ≠ 0) {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) :
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  have hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := (γ : Matrix (Fin n) (Fin n) E))
    rw [h] at this
    simp at this
  obtain ⟨z, hz, hz1, hzp⟩ := exists_norm_one s hs hs0 _ hp
  have hz' : z * star z = 1 := by rw [mul_comm]; exact hz
  have hu : (γ : Matrix (Fin n) (Fin n) E) * star (γ : Matrix (Fin n) (Fin n) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have m1 : z • (γ : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu, hz', one_smul]
  have m2 : star z • (1 : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star, star_one,
      Matrix.mul_one, hz, one_smul]
  refine ⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (γ : Matrix (Fin n) (Fin n) E) = z • (γ : Matrix (Fin n) (Fin n) E) * star z • (1 : Matrix (Fin n) (Fin n) E)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hz', one_smul]
  · show (1 - z • (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0
    rw [← eval_charpolyRev']; exact hzp
  · show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0
    have : (1 - star z • (1 : Matrix (Fin n) (Fin n) E)) = (1 - star z) • (1 : Matrix (Fin n) (Fin n) E) := by
      rw [sub_smul, one_smul]
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.mpr fun h => hz1 ?_)
    have := congrArg star h
    rw [star_one, star_star] at this
    exact this.symm

end Abstract

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem exists_skew (D : D7) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  by_contra hno
  push Not at hno
  apply NumberField.IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  have h := hno (x - star x) (by rw [star_sub, star_star]; ring)
  exact (sub_eq_zero.mp h).symm

theorem split_host (D : D7) {n : ℕ} :
    letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) D.host.E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  letI := D.host.cmStar
  intro γ
  obtain ⟨s, hs, hs0⟩ := exists_skew D
  exact split_unitary s hs hs0 γ

end Formalism.L2.PairingIndexBounds.Eq.J
