import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTEmb
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTNorm
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTGeo

noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Pos

variable (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK) (hpos : S.IsPosDef)
include hσ hsig hpos

theorem form_pos' (σ : E →+* ℂ) (x : S.V) (hx : x ≠ 0) : ∃ c : ℝ, 0 < c ∧ σ (S.hT x x) = c :=
  S.form_pos hsig σ (fun a ↦ hσ σ a) (hpos σ) x hx

theorem norm_eq_re (σ : E →+* ℂ) (x : S.V) : ‖σ (S.hT x x)‖ = (σ (S.hT x x)).re := by
  by_cases hx : x = 0
  · subst hx; simp
  · obtain ⟨c, hc, he⟩ := form_pos' S hσ hsig hpos σ x hx
    rw [he, Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.ofReal_re]

theorem trR_pos (x : S.V) (hx : x ≠ 0) : 0 < trR (S.hT x x) := by
  unfold trR
  rw [Complex.re_sum]
  have hne : (Finset.univ : Finset (E →+* ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, Embeddings.card]
    exact Module.finrank_pos
  refine Finset.sum_pos (fun σ _ ↦ ?_) hne
  obtain ⟨c, hc, he⟩ := form_pos' S hσ hsig hpos σ x hx
  rw [he, Complex.ofReal_re]; exact hc

theorem eq_zero_of_psi (M : Model S) (x : S.V) (h : psi M x = 0) : x = 0 := by
  by_contra hx
  have := trR_pos S hσ hsig hpos x hx
  rw [← norm_psi_sq M x, h, norm_zero] at this
  simp at this

theorem trR_dual_ge (q : ℕ) (hq : q ≠ 0) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (z : S.V) (hz : TrDual S L z)
    (hz0 : z ≠ 0) :
    (finrank ℚ E : ℝ) * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (finrank ℚ E : ℝ))) ≤ trR (S.hT z z) := by
  have ha : S.hT z z ≠ 0 := by
    intro h0
    have := trR_pos S hσ hsig hpos z hz0
    rw [h0] at this
    simp [trR] at this
  have h1 := one_le_norm S hσ q L hL hq z hz ha
  have hX : (0 : ℝ) < (q : ℝ) * ((discr E).natAbs : ℝ) ^ 2 := by
    have : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
    positivity
  have h1' : (1 : ℝ) ≤ |((Algebra.norm ℚ (S.hT z z) : ℚ) : ℝ)| * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  have := sum_re_ge (S.hT z z) (fun σ ↦ form_pos' S hσ hsig hpos σ z hz0) _ hX h1'
  unfold trR
  rw [Complex.re_sum]
  exact this

end Pos

section Basis

def GQ (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℚ :=
  fun i j ↦ Algebra.trace ℚ E (S.hT (e i : S.V) (e j : S.V))

theorem inner_e {S : HSpace E} (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (M : Model S)
    (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) (i j : ι) :
    ⟪psi M (e i : S.V), psi M (e j : S.V)⟫_ℝ = (GQ S L e i j : ℝ) := by
  rw [inner_psi hσ, trR_eq]; rfl

theorem psi_sum_rat {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι]
    (e : Basis ι ℤ L) (c : ι → ℚ) :
    psi M (∑ i, (c i : E) • (e i : S.V)) = ∑ i, (c i : ℝ) • psi M (e i : S.V) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ psi_rat M (c i) _

theorem psi_sum_int {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι]
    (e : Basis ι ℤ L) (c : ι → ℤ) :
    psi M (∑ i, c i • (e i : S.V)) = ∑ i, c i • psi M (e i : S.V) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ map_zsmul _ _ _

theorem GQ_det (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : (GQ S L e).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set x : S.V := ∑ i, (c i : E) • (e i : S.V) with hx
  have hnorm : ⟪psi M x, psi M x⟫_ℝ = 0 := by
    rw [hx, psi_sum_rat M L e, sum_inner]
    have : ∀ i, ⟪(c i : ℝ) • psi M (e i : S.V), ∑ j, (c j : ℝ) • psi M (e j : S.V)⟫_ℝ =
        (c i : ℝ) * (((GQ S L e) *ᵥ c) i : ℝ) := by
      intro i
      rw [real_inner_smul_left, inner_sum]
      congr 1
      simp only [real_inner_smul_right, inner_e hσ M L e, Matrix.mulVec, dotProduct]
      push_cast
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    simp only [this, hc, Pi.zero_apply, Rat.cast_zero, mul_zero, Finset.sum_const_zero]
  have hx0 : x = 0 := by
    apply eq_zero_of_psi S hσ hsig hpos M
    exact inner_self_eq_zero.1 hnorm
  apply hc0
  set m : ℕ := ∏ i, (c i).den with hm
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ (c i).den_nz
  have hdvd : ∀ i, (c i).den ∣ m := fun i ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set k : ι → ℤ := fun i ↦ ((m / (c i).den : ℕ) : ℤ) * (c i).num with hk
  have hkq : ∀ i, (k i : ℚ) = (m : ℚ) * c i := by
    intro i
    obtain ⟨t, ht⟩ := hdvd i
    have h1 : m / (c i).den = t := by
      rw [ht, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (c i).den_nz)]
    simp only [hk, h1]
    rw [ht]
    have h2 := Rat.mul_den_eq_num (c i)
    push_cast
    rw [← h2]
    ring
  have hsum : ∑ i, k i • e i = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_zero]
    have : ∀ i, ((k i • e i : L) : S.V) = (m : E) • ((c i : E) • (e i : S.V)) := by
      intro i
      have hz : ((k i • e i : L) : S.V) = k i • (e i : S.V) := by simp
      rw [hz, ← Int.cast_smul_eq_zsmul E, smul_smul]
      congr 1
      have := congrArg (fun t : ℚ ↦ (t : E)) (hkq i)
      push_cast at this
      exact this
    rw [Finset.sum_congr rfl fun i _ ↦ this i, ← Finset.smul_sum, ← hx, hx0, smul_zero]
  have hk0 := (Fintype.linearIndependent_iff.1 e.linearIndependent) k hsum
  ext i
  have := hkq i
  rw [hk0 i] at this
  simp only [Int.cast_zero, Pi.zero_apply] at this ⊢
  rcases mul_eq_zero.1 this.symm with h | h
  · exact absurd (by exact_mod_cast h) hm0
  · exact h

def GR (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℝ :=
  (GQ S L e).map (Rat.castHom ℝ)

theorem GR_det (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : (GR S L e).det ≠ 0 := by
  have h := RingHom.map_det (Rat.castHom ℝ) (GQ S L e)
  rw [RingHom.mapMatrix_apply] at h
  unfold GR
  rw [← h]
  simpa using GQ_det S hσ hsig hpos M L e

theorem GR_apply (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) (i j : ι) :
    GR S L e i j = (GQ S L e i j : ℝ) := rfl

theorem psi_e_linInd (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ fun i ↦ psi M (e i : S.V) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hG : (GR S L e) *ᵥ g = 0 := by
    ext j
    have := congrArg (fun w ↦ ⟪psi M (e j : S.V), w⟫_ℝ) hg
    simp only [inner_sum, real_inner_smul_right, inner_e hσ M L e, inner_zero_right] at this
    simp only [Matrix.mulVec, dotProduct, GR_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  exact fun i ↦ congrFun (Matrix.eq_zero_of_mulVec_eq_zero (GR_det S hσ hsig hpos M L e) hG) i

end Basis

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
