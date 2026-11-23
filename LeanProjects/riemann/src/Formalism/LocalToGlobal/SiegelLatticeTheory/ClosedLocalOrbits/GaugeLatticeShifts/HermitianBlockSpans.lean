import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianBlockSpans

open Formalism.L2.SG.HidaSetting

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_sub_left (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_sub_right (x y w : Fin n → ℂ) : hJ ε w (x - y) = hJ ε w x - hJ ε w y := by
  unfold hJ; rw [Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_sum_right {m : ℕ} (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε w (∑ i, c i • v i) = ∑ i, c i * hJ ε w (v i) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_conj (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_map {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

variable {r : ℕ}

theorem spanLt_eq (e : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r) :
    spanLt e a = Submodule.span ℂ (Set.range fun c : Fin a => e (Fin.castLE ha c)) := by
  unfold spanLt
  congr 1
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.1, hb⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Fin.castLE ha c, c.2, rfl⟩

def blk (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun b c => hJ ε (e (Fin.castLE ha b)) (e' (Fin.castLE ha c))

theorem zero_of_perp_right (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r)
    (hD : a = 0 ∨ (blk ε e e' ha).det ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ spanLt e' a) (hp : ∀ b : Fin a, hJ ε (e (Fin.castLE ha b)) x = 0) : x = 0 := by
  rw [spanLt_eq e' ha, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  rcases hD with h0 | hdet
  · subst h0
    simp
  · have hM : blk ε e e' ha *ᵥ c
        = 0 := by
      funext b
      have := hp b
      rw [hJ_sum_right] at this
      simpa [blk, Matrix.mulVec, dotProduct, mul_comm] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
    simp [this]

theorem zero_of_perp_left (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r)
    (hD : a = 0 ∨ (blk ε e e' ha).det ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ spanLt e a) (hp : ∀ b : Fin a, hJ ε x (e' (Fin.castLE ha b)) = 0) : x = 0 := by
  refine zero_of_perp_right ε e' e ha ?_ hx fun b => by rw [hJ_conj, hp b, star_zero]
  rcases hD with h0 | hdet
  · exact Or.inl h0
  · right
    have e1 : blk ε e' e ha = (blk ε e e' ha)ᴴ := by
      ext b c
      simp only [blk, Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [← hJ_conj]
    rw [e1, Matrix.det_conjTranspose]
    exact fun h => hdet (star_eq_zero.1 h)

theorem st_triv (e e' : Fin r → Fin n → ℂ) (s : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ x y, hJ ε (s *ᵥ x) (s *ᵥ y) = hJ ε x y)
    (h1 : ∀ a : Fin r, (s - 1) *ᵥ e a ∈ spanLt e a.1) (h1' : ∀ a : Fin r, (s - 1) *ᵥ e' a ∈ spanLt e' a.1)
    (h2 : ∀ y, (∀ a, hJ ε (e a) y = 0) → (s - 1) *ᵥ y ∈ spanLt e r)
    (hD : ∀ l (hl : l ≤ r), 1 ≤ l →
      (blk ε e e' hl).det ≠ 0) :
    s = 1 := by
  have hD' : ∀ l (hl : l ≤ r),
      l = 0 ∨ (blk ε e e' hl).det ≠ 0 :=
    fun l hl => by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact Or.inl h
      · exact Or.inr (hD l hl h)
  have hsub : ∀ v : Fin n → ℂ, (s - 1) *ᵥ v = s *ᵥ v - v := fun v => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]

  have step : ∀ a : ℕ, a ≤ r → ∀ c : Fin r, c.1 < a → s *ᵥ e c = e c ∧ s *ᵥ e' c = e' c := by
    intro a
    induction a with
    | zero => intro _ c hc; exact absurd hc (Nat.not_lt_zero _)
    | succ a ih =>
      intro ha c hc
      have ha' : a ≤ r := Nat.le_of_succ_le ha
      have IH := ih ha'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | heq
      · exact IH c hlt
      · have hca : c.1 = a := heq
        constructor
        · have hx := h1 c
          rw [hca] at hx
          have := zero_of_perp_left ε e e' ha' (hD' a ha') hx fun b => by
            have hb := (IH (Fin.castLE ha' b) b.2).2
            rw [hsub, hJ_sub_left, ← hb, hU, hb, sub_self]
          rw [hsub, sub_eq_zero] at this
          exact this
        · have hx := h1' c
          rw [hca] at hx
          have := zero_of_perp_right ε e e' ha' (hD' a ha') hx fun b => by
            have hb := (IH (Fin.castLE ha' b) b.2).1
            rw [hsub, hJ_sub_right, ← hb, hU, hb, sub_self]
          rw [hsub, sub_eq_zero] at this
          exact this
  have hfix : ∀ c : Fin r, s *ᵥ e c = e c ∧ s *ᵥ e' c = e' c := fun c => step r le_rfl c c.2

  ext i j
  suffices hall : ∀ y : Fin n → ℂ, s *ᵥ y = y by
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using this
  intro y
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hy := h2 y (fun a => a.elim0)
    have h0 : spanLt e 0 = ⊥ := by
      unfold spanLt
      simp
    rw [h0, Submodule.mem_bot, hsub, sub_eq_zero] at hy
    exact hy
  · let M : Matrix (Fin r) (Fin r) ℂ := fun b c => hJ ε (e b) (e' c)
    have hMdet : M.det ≠ 0 := hD r le_rfl hr
    let lam : Fin r → ℂ := M⁻¹ *ᵥ fun b => hJ ε (e b) y
    let x' : Fin n → ℂ := ∑ c, lam c • e' c
    have hMl : M *ᵥ lam = fun b => hJ ε (e b) y := by
      simp only [lam, Matrix.mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hMdet), Matrix.one_mulVec]
    have hperp : ∀ b, hJ ε (e b) (y - x') = 0 := by
      intro b
      rw [hJ_sub_right, hJ_sum_right]
      have := congrFun hMl b
      simp only [Matrix.mulVec, dotProduct, M] at this
      rw [← this]
      simp only [mul_comm, sub_self]
    have hx'fix : s *ᵥ x' = x' := by
      simp only [x', Matrix.mulVec_sum, Matrix.mulVec_smul, (hfix _).2]
    have hw : (s - 1) *ᵥ y ∈ spanLt e r := by
      have := h2 (y - x') hperp
      rwa [Matrix.mulVec_sub, hsub x', hx'fix, sub_self, sub_zero] at this
    have hw0 := zero_of_perp_left ε e e' le_rfl (hD' r le_rfl) hw fun b => by
      have hb := (hfix (Fin.castLE le_rfl b)).2
      rw [hsub, hJ_sub_left, ← hb, hU, hb, sub_self]
    rw [hsub, sub_eq_zero] at hw0
    exact hw0

end Formalism.L2.SG.RealObj.HermitianBlockSpans
