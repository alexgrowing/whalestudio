import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoeffOfValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangularFactorMiddleRow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddProjectionMemIsotropicSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

section nf

variable {k r : ℕ}

theorem zb_last_row (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (a b : ℕ) (ha : a ≠ i0)
    (ha' : a + 1 < i0 + s) (hb : b = i0) : C3.Zb i0 s hh t a b = 0 := by
  subst hb
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem zb_col_last (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (a : ℕ) (ha : a ≠ i0)
    (ha' : a + 1 < i0 + s) : C3.Zb i0 s hh t a (i0 + s - 1) = 0 := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem corner_matrix_last_entry (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) :
    C3.Zb i0 s hh t i0 (i0 + s - 1) = t := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem corner_matrix_first_line_zero (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hs : 2 ≤ s) (b : ℕ) (hb : b + 1 < i0 + s) :
    C3.Zb i0 s hh t i0 b = 0 := by
  unfold C3.Zb
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem herm_bvec_right (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec p) = WeylGroupFacts.sgn k r p * v (WeylGroupFacts.tau k r p) := by
  have hs : star (Pi.single p (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single p 1 := by
    ext q
    by_cases h : q = p
    · subst h
      simp
    · simp [Pi.single_apply, h]
  unfold herm bvec
  rw [hs, single_dotProduct, one_mul, SignAntidiagonal.mulVec_hpk]

theorem nf_top (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hT' : herm (Hpk k r) z' z' ≠ 0)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : γ ∈ UH (Hpk k r)) (i0 s : ℕ) (hs : 2 ≤ s)
    (hj : i0 + s = r + 1) (hh : Matrix (Fin i0) (Fin i0) ℂ) (hdet : hh.det ≠ 0) (t : ℂ) (ht : t ≠ 0)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' γ a b = C3.Zb i0 s hh t a.val b.val) :
    ∃ n0 ∈ C3.N0set k r z', ∃ yb : Fin (2 * r + k + 1) → ℂ, inWb k r yb ∧ herm (Hpk k r) z' yb = t ∧
      (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
        PBG.xi0 (γ * n0) a p = if p.val < r ∧ p.val ≠ i0 then C3.Zb i0 s hh t a.val p.val else 0) ∧
      (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → PBG.xi0 (γ * n0) a p = herm (Hpk k r) (bvec p) yb) := by
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  have hγi : γ⁻¹ ∈ UH (Hpk k (i0 + s'' + 1)) := WeylGroupFacts.uh_inv hγ
  have hγu := WeylGroupFacts.isUnit_of_uh hγ
  set y : Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) → ℂ := fun a => γ⁻¹ *ᵥ bvec (eI k _ a) with hy
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hi

  have hyS : ∀ (a b : Fin (i0 + s'' + 1)), y a (esI k _ b) = star (C3.Zb i0 (s'' + 2) hh t a.val b.val) := by
    intro a b
    simp only [hy]
    rw [(xi_Y_zhat_identity k _ z z' γ a b hγ).2, hZ]
    rfl
  have hfz' : fvec k (i0 + s'' + 1) z' (Fin.last _) = z' := by unfold fvec; rw [dif_neg (by simp)]
  have hfa : ∀ a : Fin (i0 + s'' + 1), fvec k _ z a.castSucc = bvec (eI k _ a) := by
    intro a; unfold fvec; rw [dif_pos (by have := a.isLt; simp; omega)]; rfl
  have hyz : ∀ a : Fin (i0 + s'' + 1), herm (Hpk k _) z' (y a) = C3.Zb i0 (s'' + 2) hh t a.val (i0 + s'' + 1) := by
    intro a
    have h1 : herm (Hpk k _) z' (y a) = herm (Hpk k _) (γ *ᵥ z') (γ *ᵥ y a) := (herm_unitary γ hγ _ _).symm
    have h2 : γ *ᵥ y a = bvec (eI k _ a) := by
      rw [hy]; simp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mulVec]
    rw [h1, h2]
    have := hZ a.castSucc (Fin.last _)
    simp only [Zhat, hfz', hfa] at this
    rw [this]
    simp
  obtain ⟨n0, hn0, y', hy'⟩ := isotropicNormalFormFull_statement k (i0 + s'') z' i y t hz' hT' ht
    (by
      intro a ha
      rw [hyS]
      have : C3.Zb i0 (s'' + 2) hh t a.val i0 = 0 :=
        zb_last_row i0 _ hh t (by omega) a.val i0 (fun h => ha (Fin.ext h)) (by omega) rfl
      show star (C3.Zb i0 (s'' + 2) hh t a.val i0) = 0
      rw [this, star_zero])
    (by
      intro p hp
      have hb : 2 * (i0 + s'' + 1) + k - p.val < i0 + s'' + 1 := by omega
      have hpe : p = esI k _ ⟨2 * (i0 + s'' + 1) + k - p.val, hb⟩ := by ext; simp [esI]; omega
      rw [hpe, hyS]
      have : C3.Zb i0 (s'' + 2) hh t i0 (2 * (i0 + s'' + 1) + k - p.val) = 0 :=
        corner_matrix_first_line_zero i0 _ hh t (by omega) _ (by omega)
      simp [hi, this])
    (by
      have hP := third_polynomial_expansion i0 s'' hh t
      have hS := (sign_permutation_identity s'').2
      have hsg : C3.sgnW s'' ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hS; exact (by norm_num : (0 : ℂ) ≠ -1) hS
      have hne : (Matrix.of fun a b : Fin (i0 + s'') => C3.Zb i0 (s'' + 2) hh t
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).det ≠ 0 := by
        rw [hP]; exact mul_ne_zero (mul_ne_zero hdet (pow_ne_zero _ ht)) hsg
      have e : (Matrix.of fun a b : Fin (i0 + s'') => y (i.succAbove a) (esI k (i0 + s'' + 1) (i.succAbove b))) =
          (Matrix.of fun a b : Fin (i0 + s'') => C3.Zb i0 (s'' + 2) hh t
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).map (starRingEnd ℂ) := by
        ext a b; simp [hyS, hi]
      rw [e]
      change ((starRingEnd ℂ).mapMatrix _).det ≠ 0
      rw [← RingHom.map_det]
      exact (map_ne_zero _).2 hne)
    (by
      intro a ha
      rw [hyz]
      have := zb_col_last i0 (s'' + 2) hh t (by omega) a.val (fun h => ha (Fin.ext h)) (by omega)
      rwa [show i0 + (s'' + 2) - 1 = i0 + s'' + 1 by omega] at this)
    (by
      rw [hyz]
      have := corner_matrix_last_entry i0 (s'' + 2) hh t (by omega)
      rwa [show i0 + (s'' + 2) - 1 = i0 + s'' + 1 by omega] at this)
    (by
      intro a a'
      rw [hy]; simp only
      rw [herm_unitary _ hγi, herm_bvec_bvec]
      have := a.isLt
      have := a'.isLt
      unfold Hpk
      rw [if_neg (fun h => by simp only [eI] at h; omega), if_neg (fun h => by simp only [eI] at h; omega),
        if_neg (fun h => by simp only [eI] at h; omega)])

  have hn0u : n0 ∈ UH (Hpk k (i0 + s'' + 1)) := hn0.1
  have hxi : ∀ (a : Fin (i0 + s'' + 1)) (p : Fin (2 * (i0 + s'' + 1) + k + 1)),
      PBG.xi0 (γ * n0) a p = herm (Hpk k _) (bvec p) (y' a) := by
    intro a p
    unfold PBG.xi0
    have h2 : bvec (eI k _ a) = γ *ᵥ y a := by
      rw [hy]; simp only
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mulVec]
    rw [h2, ← Matrix.mulVec_mulVec, herm_unitary γ hγ, ← (hy' a).1, herm_unitary n0 hn0u]
  refine ⟨n0, hn0, y' i, ((hy' i).2.2 rfl).1, ((hy' i).2.2 rfl).2, ?_, ?_⟩
  · intro a p ha
    have hai : a ≠ i := fun h => ha (by rw [h])
    obtain ⟨hz0, hsame⟩ := (hy' a).2.1 hai
    rw [hxi, herm_swap, herm_bvec_right]
    by_cases hp : p.val < i0 + s'' + 1
    ·
      have htau : WeylGroupFacts.tau k _ p = esI k _ ⟨p.val, hp⟩ := by
        ext; rw [tau_val, if_pos (Or.inl hp)]; simp [esI]
      have hsg : WeylGroupFacts.sgn k _ p = 1 := sgn_one _ (by omega)
      rw [htau, hsg, one_mul, hsame _ (by simp [esI]; omega), hyS, star_star]
      by_cases hpi : p.val = i0
      · rw [if_neg (by omega)]
        exact zb_last_row i0 _ hh t (by omega) a.val p.val ha (by omega) hpi
      · rw [if_pos ⟨hp, hpi⟩]
    · rw [if_neg (by omega)]
      have hle : (WeylGroupFacts.tau k _ p).val ≤ i0 + s'' + 1 + k := by
        rw [tau_val]; split_ifs <;> omega
      rw [hz0 _ hle]
      simp
  · intro a p ha
    have hai : a = i := Fin.ext ha
    subst hai
    rw [hxi]

end nf

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
