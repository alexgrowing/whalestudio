import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) : Frame Ψ r :=
  fun τ k a => τ.1 (u a k)

theorem col_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) (τ : Ψ) (a : Fin r) :
    col (mat (frm Ψ u) τ) a = Data.emb τ.1 (u a) := rfl

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem hermC_emb {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem im_emb_herm_self {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : (τ (herm G x x)).im = 0 := by
  have h2 : conj (τ (herm G x x)) = τ (herm G x x) := by
    rw [← emb_cc, HermitianTraceFormVanishing.herm_conj G hG x x]
  exact Complex.conj_eq_iff_im.1 h2

theorem dmin_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem psgn_mul_dmin {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (p0 : ℕ)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    psgn p0 i * (dmin G (frm Ψ u) τ i).re = ∏ k : Fin i, (sgn p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) k : Fin r) *
      (τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))).re) := by
  have hr : ∀ w : Fin r → E, τ.1 (herm G w w) = ((τ.1 (herm G w w)).re : ℂ) := fun w =>
    Complex.ext (by simp) (by simp [im_emb_herm_self τ.1 G hG w])
  rw [dmin_frm Ψ G u ho τ i, Finset.prod_mul_distrib, psgn, ← Fin.prod_univ_eq_prod_range]
  congr 1
  rw [Finset.prod_congr rfl (fun k _ => hr _), ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_succ {r : ℕ} (f : Fin r → ℝ) (j : Fin r) :
    ∏ k : Fin (j.succ : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k) =
      (∏ k : Fin (j.castSucc : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)) * f j := by
  change ∏ k : Fin ((j : ℕ) + 1), f (Fin.castLE _ k) = (∏ k : Fin (j : ℕ), f (Fin.castLE _ k)) * f j
  rw [Fin.prod_univ_castSucc]
  rfl

theorem sign_of_mem {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hu : frm X.Ψ u ∈ X.dom) (τ : X.Ψ) (j : Fin r) :
    0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re := by
  have h1 := (hu τ).2 j.succ
  have h0 := (hu τ).2 j.castSucc
  rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ] at h1 h0
  rw [prod_succ (fun k => sgn X.p0 k * (τ.1 (herm X.Gm (u k) (u k))).re)] at h1
  exact (pos_iff_pos_of_mul_pos h1).1 h0

theorem mem_of_sign {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hd : (Matrix.of u).det ≠ 0)
    (hs : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re) : frm X.Ψ u ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have : mat (frm X.Ψ u) τ = τ.1.mapMatrix (Matrix.of u).transpose := by
      ext k a; rfl
    rw [this, ← RingHom.map_det, Matrix.det_transpose]
    exact (map_ne_zero τ.1).2 hd
  · rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ]
    exact Finset.prod_pos fun k _ => hs τ _

end

end GlobalTheory.OrthoFrame
