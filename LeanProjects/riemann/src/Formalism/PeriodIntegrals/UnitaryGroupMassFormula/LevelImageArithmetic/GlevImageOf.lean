import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

noncomputable section

namespace QnGlevImageW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

local macro "ifarith" : tactic =>
  `(tactic| (split_ifs <;> first | rfl | (exfalso; omega)))

lemma mulVec_bvec {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (q : Fin m) :
    g *ᵥ bvec q = fun p => g p q := by
  ext p
  simp [bvec, Matrix.mulVec_single]

lemma levPos_mem (k i r' : ℕ) (x : Fin (2 * r' + k + 1)) :
    i ≤ (levPos k i r' x).val ∧ (levPos k i r' x).val < 2 * r' + k + 1 + i := by
  have := x.isLt
  simp only [levPos]
  exact ⟨by omega, by omega⟩

lemma sum_block (k i r' : ℕ) (f : Fin (2 * (i + r') + k + 1) → ℂ)
    (hf : ∀ x : Fin (2 * (i + r') + k + 1), ¬(i ≤ x.val ∧ x.val < 2 * r' + k + 1 + i) → f x = 0) :
    ∑ x, f x = ∑ x' : Fin (2 * r' + k + 1), f (levPos k i r' x') := by
  symm
  refine Finset.sum_bij_ne_zero (fun x' _ _ => levPos k i r' x') (fun _ _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ _ => rfl)
  · intro a _ _ b _ _ h
    simp only [levPos, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro y _ hy
    have hin : i ≤ y.val ∧ y.val < 2 * r' + k + 1 + i := by
      by_contra h
      exact hy (hf y h)
    have hy' : levPos k i r' ⟨y.val - i, by omega⟩ = y := Fin.ext (by simp only [levPos]; omega)
    exact ⟨⟨y.val - i, by omega⟩, Finset.mem_univ _, by rw [hy']; exact hy, hy'⟩

lemma hpk_shift (k i r' : ℕ) (s t : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' s) (levPos k i r' t) = Hpk k r' s t := by
  have := s.isLt
  have := t.isLt
  show Hpk k (i + r') ⟨s.val + i, by omega⟩ ⟨t.val + i, by omega⟩ = _
  simp only [Hpk, Fin.ext_iff]
  ifarith

lemma hpk_partner (k i r' : ℕ) (X p : Fin (2 * (i + r') + k + 1)) (hXv : X.val = 2 * (i + r') + k - p.val)
    (hp : ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) (y : Fin (2 * (i + r') + k + 1)) :
    Hpk k (i + r') X y = if y = p then 1 else 0 := by
  have hX := X.isLt
  have hy := y.isLt
  have hp' := p.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  ifarith

theorem glevImage_of (_hH : LevHom) (hU : LevUH) : GlevImage := by
  intro k i r'
  ext g
  constructor
  · rintro ⟨hg, hfix⟩
    have hg' : gᴴ * Hpk k (i + r') * g = Hpk k (i + r') := hg
    have hcol : ∀ q : Fin (2 * (i + r') + k + 1), ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) →
        ∀ p, g p q = if p = q then 1 else 0 := by
      intro q hq p
      have hqlt := q.isLt
      by_cases hqi : q.val < i
      · have h := (hfix ⟨q.val, by omega⟩ (by simpa using hqi)).1
        have e : eI k (i + r') ⟨q.val, by omega⟩ = q := Fin.ext (by simp [eI])
        rw [e, mulVec_bvec] at h
        have := congrFun h p
        simpa [bvec, Pi.single_apply] using this
      · have h := (hfix ⟨2 * (i + r') + k - q.val, by omega⟩ (by simp; omega)).2
        have e : esI k (i + r') ⟨2 * (i + r') + k - q.val, by omega⟩ = q := Fin.ext (by simp [esI]; omega)
        rw [e, mulVec_bvec] at h
        have := congrFun h p
        simpa [bvec, Pi.single_apply] using this
    have hrow : ∀ p : Fin (2 * (i + r') + k + 1), ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) →
        ∀ Q, g p Q = if Q = p then 1 else 0 := by
      intro p hp Q
      have hplt := p.isLt
      obtain ⟨X, hXv⟩ : ∃ X : Fin (2 * (i + r') + k + 1), X.val = 2 * (i + r') + k - p.val :=
        ⟨⟨2 * (i + r') + k - p.val, by omega⟩, rfl⟩
      have hX : ¬(i ≤ X.val ∧ X.val < 2 * r' + k + 1 + i) := by omega
      have h1 : ∀ y, (gᴴ * Hpk k (i + r')) X y = Hpk k (i + r') X y := by
        intro y
        rw [Matrix.mul_apply]
        simp only [conjTranspose_apply, hcol X hX]
        rw [Finset.sum_eq_single X (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ X) h)]
        simp
      have h2 := congrFun (congrFun hg' X) Q
      rw [Matrix.mul_apply] at h2
      simp only [h1, hpk_partner k i r' X p hXv hp, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
      exact h2
    have hblk : ∀ p q : Fin (2 * (i + r') + k + 1), ¬(i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) →
        (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) → g p q = 0 := by
      intro p q hp hq
      rw [hrow p hp q, if_neg]
      rintro rfl
      exact hp hq
    refine ⟨Matrix.of fun x y => g (levPos k i r' x) (levPos k i r' y), ?_, ?_⟩
    · show _ = _
      ext s t
      have h := congrFun (congrFun hg' (levPos k i r' s)) (levPos k i r' t)
      rw [hpk_shift] at h
      rw [← h, Matrix.mul_apply, Matrix.mul_apply,
        sum_block k i r' (fun Y => (gᴴ * Hpk k (i + r')) (levPos k i r' s) Y * g Y (levPos k i r' t))
          (fun Y hY => by simp only [hblk Y _ hY (levPos_mem k i r' t), mul_zero])]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      congr 1
      rw [Matrix.mul_apply, Matrix.mul_apply,
        sum_block k i r' (fun x => (gᴴ) (levPos k i r' s) x * Hpk k (i + r') x (levPos k i r' y))
          (fun x hx => by simp only [conjTranspose_apply, hblk x _ hx (levPos_mem k i r' s), star_zero, zero_mul])]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [conjTranspose_apply, hpk_shift, Matrix.of_apply]
    · ext p q
      simp only [ιLev, Matrix.of_apply]
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · rw [dif_pos hp]
        by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
        · rw [dif_pos hq]
          congr 1 <;> (apply Fin.ext; simp only [levPos]; omega)
        · rw [dif_neg hq, hcol q hq p, if_neg]
          rintro rfl
          exact hq hp
      · rw [dif_neg hp, hrow p hp q]
        rcases eq_or_ne p q with h | h
        · subst h; simp
        · simp [h, h.symm]
  · rintro ⟨g₀, hg₀, rfl⟩
    refine ⟨hU k i r' g₀ hg₀, ?_⟩
    intro a ha
    have ha' : a.val < i := ha
    have := a.isLt
    constructor
    · rw [mulVec_bvec]
      funext p
      have := p.isLt
      dsimp only [ιLev, bvec, eI]
      simp only [Pi.single_apply, Fin.ext_iff]
      ifarith
    · rw [mulVec_bvec]
      funext p
      have := p.isLt
      dsimp only [ιLev, bvec, esI]
      simp only [Pi.single_apply, Fin.ext_iff]
      ifarith

end QnGlevImageW
