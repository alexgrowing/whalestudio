import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixFirstLineZero

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

section entries

theorem ptEntry_cons (s1 : ℕ) (t1 : ℂ) (rest : C.LPt) (a b : ℕ) :
    D.ptEntry ((s1, t1) :: rest) a b =
      if a < s1 ∧ b < s1 then (if a + b + 1 = s1 then t1 else 0)
      else if s1 ≤ a ∧ s1 ≤ b then D.ptEntry rest (a - s1) (b - s1) else 0 := rfl

theorem ptEntry_append (h : C.LPt) (s : ℕ) (t : ℂ) (a b : ℕ) :
    D.ptEntry (h ++ [(s, t)]) a b =
      if a < D.ptSize h ∧ b < D.ptSize h then D.ptEntry h a b
      else if D.ptSize h ≤ a ∧ D.ptSize h ≤ b then
        (if a - D.ptSize h < s ∧ b - D.ptSize h < s ∧ (a - D.ptSize h) + (b - D.ptSize h) + 1 = s then t else 0)
      else 0 := by
  induction h generalizing a b with
  | nil =>
    simp only [List.nil_append, D.ptSize, List.map_nil, List.sum_nil, Nat.sub_zero]
    rw [ptEntry_cons]
    simp only [D.ptEntry]
    split_ifs <;> first | rfl | omega
  | cons blk h ih =>
    obtain ⟨s1, t1⟩ := blk
    have hsz : D.ptSize ((s1, t1) :: h) = s1 + D.ptSize h := by simp [D.ptSize]
    rw [List.cons_append, hsz, ptEntry_cons, ih]
    split_ifs <;> first | rfl | omega | (rw [ptEntry_cons]; split_ifs <;> first | rfl | omega)

theorem ptMatN_zb (h : C.LPt) (s : ℕ) (t : ℂ) (n : ℕ) (hn : n = D.ptSize h + s) (a b : Fin n) :
    D.ptMatN (h ++ [(s, t)]) n a b = C3.Zb (D.ptSize h) s (D.ptMatN h (D.ptSize h)) t a.val b.val := by
  unfold D.ptMatN
  rw [ptEntry_append]
  unfold C3.Zb
  have ha := a.isLt
  have hb := b.isLt
  by_cases h1 : a.val < D.ptSize h
  · rw [dif_pos h1]
    by_cases h2 : b.val < D.ptSize h
    · rw [if_pos ⟨h1, h2⟩, dif_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega), dif_neg h2]
  · rw [dif_neg h1, if_neg (fun h => h1 h.1)]
    by_cases h2 : D.ptSize h ≤ b.val
    · rw [if_pos ⟨by omega, h2⟩]
      by_cases h3 : a.val - D.ptSize h + (b.val - D.ptSize h) + 1 = s
      · rw [if_pos ⟨by omega, by omega, h3⟩, if_pos ⟨h2, by omega, by omega, h3⟩]
      · rw [if_neg (fun h => h3 h.2.2), if_neg (fun h => h3 h.2.2.2)]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.1)]

end entries

section point

variable {k r : ℕ}

theorem corner_matrix_right_translate (z z' : Fin (2 * r + k + 1) → ℂ) (γ n0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hn0 : n0 ∈ C3.N0set k r z') : Zhat k r z z' (γ * n0) = Zhat k r z z' γ := by
  ext a b
  unfold Zhat
  rw [← Matrix.mulVec_mulVec]
  congr 2
  unfold fvec
  split_ifs with hb
  · exact hn0.2.1 ⟨b.val, hb⟩
  · exact hn0.2.2.1

theorem dmin_zb (z z' : Fin (2 * r + k + 1) → ℂ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' x a b = C3.Zb i0 s hh t a.val b.val) (l : Fin (r + 2)) :
    Dmin k r z z' x l = C3.Dlead i0 s hh t l.val := by
  unfold Dmin C3.Dlead
  congr 1
  ext a b
  rw [Matrix.submatrix_apply, hZ]
  rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem La_one (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) : La hD K hK x₁ 1 = K x₁ := by
  show ((vK hD K hK : VS k r 0 D E) : Q.Mx k r → E) x₁ = K x₁
  exact cut_of_mem K hx₁

theorem top_poly (hD : IsOpen D) (z z' yb : Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (hs : 2 ≤ s) (hj : i0 + s = r + 1)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hdet : hh.det ≠ 0) (ht : t ≠ 0) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (hz' : inWb k r z') (hyb : inWb k r yb) (hzy : herm (Hpk k r) z' yb = t)
    (hnf1 : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
      xi0 x₁ a p = if p.val < r ∧ p.val ≠ i0 then C3.Zb i0 s hh t a.val p.val else 0)
    (hnf2 : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → xi0 x₁ a p = herm (Hpk k r) (bvec p) yb)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' x₁ a b = C3.Zb i0 s hh t a.val b.val)
    (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g) :
    ∃ c : Fin (i0 + 1) → E, c (Fin.last i0) = ((-1) ^ (s - 1) / t) • K x₁ ∧
      ∀ y : ℝ, (Dmin k r z z' x₁ (Fin.last _))⁻¹ •
          C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) K x₁ =
        ∑ n : Fin (i0 + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  have hi0 : i0 ≤ r := by omega
  have hDl : ∀ l : Fin (r + 2), Dmin k r z z' x₁ l = C3.Dlead i0 s hh t l.val := dmin_zb z z' x₁ i0 s hh t hZ
  have hDi0 : C3.Dlead i0 s hh t i0 = hh.det := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).1
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity (Module.End ℂ (VS k r 0 D E)) k r (E0 hD) (xi0 x₁) i0 hi0
  have hdetxi : (Matrix.of fun a b : Fin i0 => xi0 x₁ (Fin.castLE hi0 a) (C3.xR k r i0 hi0 b)).det = hh.det := by
    rw [det_upper_minor_eq_minor z z' x₁ i0 hi0, hDl, ← hDi0]

  have hpoly : PolyRepN i0 (fun u => (Dmin k r z z' x₁ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K x₁)
      (((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁) := by
    refine ⟨fun l => if hl : l < i0 then ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((hh.det)⁻¹ • La hD K hK x₁ (B ⟨l, hl⟩))
      else ((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁, by simp, fun u => ?_⟩
    have hE := Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion (Module.End ℂ (VS k r 0 D E)) E k r z' yb (E0 hD) (La hD K hK x₁)
      (xi0 x₁) i0 s hh t u hs hj (La_rule hD z' K hK hR x₁) hdet ht hz' hyb hzy hnf1 hnf2
    rw [La_AAx hD K hK x₁ hx₁] at hE
    have hlast : Dmin k r z z' x₁ (Fin.last (r + 1)) = C3.Dlead i0 s hh t (r + 1) := by rw [hDl]; rfl
    simp only
    rw [hlast, hE, hDi0, hB u]
    simp only [map_add, map_sum, Finset.sum_range_succ, dif_neg (lt_irrefl i0)]
    have hm : ∀ (c : ℂ) (X : Module.End ℂ (VS k r 0 D E)),
        La hD K hK x₁ (algebraMap ℂ (Module.End ℂ (VS k r 0 D E)) c * X) = c • La hD K hK x₁ X := by
      intro c X
      rw [← Algebra.smul_def, map_smul]
    have ha : ∀ c : ℂ, La hD K hK x₁ (algebraMap ℂ (Module.End ℂ (VS k r 0 D E)) c) = c • K x₁ := by
      intro c
      rw [← mul_one (algebraMap ℂ _ c), hm, La_one hD K hK x₁ hx₁]
    rw [ha, Finset.sum_range (fun l => u ^ l • if hl : l < i0 then ((-1 : ℂ) ^ (s - 1) * t⁻¹) •
      ((hh.det)⁻¹ • La hD K hK x₁ (B ⟨l, hl⟩)) else ((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁)]
    simp only [hm, dif_pos (Fin.isLt _), Fin.eta]
    rw [smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro l _
      rw [smul_comm ((hh.det)⁻¹) (u ^ (l : ℕ)), smul_comm ((-1 : ℂ) ^ (s - 1) * t⁻¹) (u ^ (l : ℕ))]
    · simp only [smul_smul]
      rw [hdetxi]
      congr 1
      field_simp
  obtain ⟨c, hc, hf⟩ := polyRepN_shift hpoly (((2 * r + k : ℕ) : ℂ) / 2)
  refine ⟨fun n => c n.val, ?_, fun y => ?_⟩
  · simp only [Fin.val_last]
    rw [hc, div_eq_mul_inv]
  · have := hf (y : ℂ)
    simp only at this
    rw [this, Fin.sum_univ_eq_sum_range (fun l => ((y : ℂ) ^ l) • c l)]

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
