import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd

noncomputable section

namespace GlobalTheory.SplitTorus

variable {n : ℕ} (ε : Fin n → Bool)

def bJ (u y : Fin n → ℂ) : ℂ := star u ⬝ᵥ (Jm ε *ᵥ y)

theorem jm_mul_self : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

theorem jm_conjTranspose : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a; by_cases h : ε a <;> simp [h]

theorem jm_jm_mulVec (y : Fin n → ℂ) : Jm ε *ᵥ (Jm ε *ᵥ y) = y := by
  rw [mulVec_mulVec, jm_mul_self, one_mulVec]

variable {ε}

theorem coord {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (b : Fin n) (y : Fin n → ℂ) :
    bJ ε (P *ᵥ Pi.single b 1) y = ((Pᴴ * Jm ε * P) *ᵥ (P⁻¹ *ᵥ y)) b := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  conv_lhs => rw [show y = P *ᵥ (P⁻¹ *ᵥ y) by rw [mulVec_mulVec, hPP, one_mulVec]]
  rw [bJ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp [Pi.star_def, Pi.single_apply, dotProduct]

theorem row_p {P : Matrix (Fin n) (Fin n) ℂ} {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    (z : Fin n → ℂ) : ((Pᴴ * Jm ε * P) *ᵥ z) p = z q := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single q]
  · rw [hG p q (Or.inl rfl)]; simp
  · intro b _ hb; rw [hG p b (Or.inl rfl)]; simp [hb, hpq]
  · simp

theorem row_q {P : Matrix (Fin n) (Fin n) ℂ} {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    (z : Fin n → ℂ) : ((Pᴴ * Jm ε * P) *ᵥ z) q = z p := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p]
  · rw [hG q p (Or.inr (Or.inl rfl))]; simp
  · intro b _ hb; rw [hG q b (Or.inr (Or.inl rfl))]; simp [hb, hpq.symm]
  · simp

theorem act {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    (d : Fin n → ℂ) (hd : ∀ a, a ≠ p → a ≠ q → d a = 1) (y : Fin n → ℂ) :
    (P * diagonal d * P⁻¹) *ᵥ y = y + ((d p - 1) * bJ ε (P *ᵥ Pi.single q 1) y) • (P *ᵥ Pi.single p 1)
      + ((d q - 1) * bJ ε (P *ᵥ Pi.single p 1) y) • (P *ᵥ Pi.single q 1) := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  rw [coord hP q, coord hP p, row_q hpq hG, row_p hpq hG]
  have hy : P *ᵥ (P⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, hPP, one_mulVec]
  have hdz : diagonal d *ᵥ (P⁻¹ *ᵥ y) = (P⁻¹ *ᵥ y) + ((d p - 1) * (P⁻¹ *ᵥ y) p) • Pi.single p 1
      + ((d q - 1) * (P⁻¹ *ᵥ y) q) • Pi.single q 1 := by
    funext a
    simp only [mulVec_diagonal, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hap : a = p
    · subst hap; simp [hpq]; ring
    · by_cases haq : a = q
      · subst haq; simp [hap]; ring
      · simp [hap, haq, hd a hap haq]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hdz, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hy]

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_lie_conj {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (d : Fin n → ℂ)
    (hd : ∀ a b, (star (d a) + d b) * (Pᴴ * Jm ε * P) a b = 0) :
    P * diagonal d * P⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet ε := by
  have hPPi : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  have e1 : ∀ M : Matrix (Fin n) (Fin n) ℂ, P⁻¹ᴴ * (Pᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hPPi, conjTranspose_one, Matrix.one_mul]
  have h0 : diagonal (star d) * (Pᴴ * Jm ε * P) + (Pᴴ * Jm ε * P) * diagonal d = 0 := by
    ext a b
    simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, Pi.star_apply, Matrix.zero_apply]
    linear_combination hd a b
  show (P * diagonal d * P⁻¹)ᴴ * Jm ε + Jm ε * (P * diagonal d * P⁻¹) = 0
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose]
  calc _ = P⁻¹ᴴ * (diagonal (star d) * (Pᴴ * Jm ε * P) + (Pᴴ * Jm ε * P) * diagonal d) * P⁻¹ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hPPi, Matrix.mul_one, e1]
    _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]

theorem toM_expG_conj {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (d : Fin n → ℂ)
    (hX : inG ε (P * diagonal d * P⁻¹)) (t : ℝ) :
    toM (expG ε (P * diagonal d * P⁻¹) t) = P * diagonal (fun a => Complex.exp (t * d a)) * P⁻¹ := by
  rw [toM_expG ε _ t hX]
  rw [show (t : ℂ) • (P * diagonal d * P⁻¹) = P * diagonal ((t : ℂ) • d) * P⁻¹ by
    rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]]
  rw [Matrix.exp_conj _ _ hP, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  rfl

theorem conjT_eq {M N : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ * Jm ε * M = Jm ε) (hMN : M * N = 1) :
    Mᴴ = Jm ε * N * Jm ε := by
  calc Mᴴ = Mᴴ * (Jm ε * (M * N) * Jm ε) := by rw [hMN, Matrix.mul_one, jm_mul_self, Matrix.mul_one]
    _ = (Mᴴ * Jm ε * M) * N * Jm ε := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM]

theorem bJ_twist (c : ℂ) (e y : Fin n → ℂ) :
    bJ ε (c • (Jm ε *ᵥ e)) (Jm ε *ᵥ y) = star c * bJ ε e y := by
  rw [bJ, bJ, jm_jm_mulVec, star_smul, smul_dotProduct, star_mulVec, jm_conjTranspose,
    ← dotProduct_mulVec, smul_eq_mul]

theorem col_ne_zero {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (p : Fin n) :
    P *ᵥ Pi.single p (1 : ℂ) ≠ 0 := by
  intro h0
  have h1 : P⁻¹ *ᵥ (P *ᵥ Pi.single p (1 : ℂ)) = Pi.single p 1 := by
    rw [mulVec_mulVec, nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP), one_mulVec]
  rw [h0, mulVec_zero] at h1
  have := congrFun h1 p
  simp at this

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem bJ_smul_left (t : ℂ) (u y : Fin n → ℂ) : bJ ε (t • u) y = star t * bJ ε u y := by
  rw [bJ, bJ, star_smul, smul_dotProduct, smul_eq_mul]

theorem bJ_smul_right (t : ℂ) (u y : Fin n → ℂ) : bJ ε u (t • y) = t * bJ ε u y := by
  rw [bJ, bJ, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem act_col {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (d : Fin n → ℂ) (b : Fin n) :
    (P * diagonal d * P⁻¹) *ᵥ (P *ᵥ Pi.single b 1) = d b • (P *ᵥ Pi.single b 1) := by
  have hPiP : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP)
  rw [mulVec_mulVec, Matrix.mul_assoc, hPiP, Matrix.mul_one, ← mulVec_mulVec, ← mulVec_smul]
  congr 1
  funext a
  simp only [mulVec_diagonal, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

theorem conj_mul_conj {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (d d' : Fin n → ℂ)
    (hdd : ∀ a, d a * d' a = 1) : (P * diagonal d * P⁻¹) * (P * diagonal d' * P⁻¹) = 1 := by
  have hPiP : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP)
  have hPPi : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  have h1 : diagonal d * diagonal d' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact hdd a
  calc _ = P * (diagonal d * (P⁻¹ * P) * diagonal d') * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hPiP, Matrix.mul_one, h1, Matrix.mul_one, hPPi]

theorem keep {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
    {c : ℂ} (hc : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)))
    (d d' : Fin n → ℂ) (hd : ∀ a, a ≠ p → a ≠ q → d a = 1) (hd' : ∀ a, a ≠ p → a ≠ q → d' a = 1)
    (hdd : ∀ a, d a * d' a = 1) (M : Matrix (Fin n) (Fin n) ℂ) (hMd : M = P * diagonal d * P⁻¹)
    (hM : Mᴴ * Jm ε * M = Jm ε) (y : Fin n → ℂ) (hy : bJ ε (P *ᵥ Pi.single p 1) y = 0) :
    (∃ s : ℂ, M *ᵥ y = y + s • (P *ᵥ Pi.single p 1)) ∧
      ∃ s : ℂ, Mᴴ *ᵥ y = y + s • (P *ᵥ Pi.single p 1) := by
  constructor
  · exact ⟨_, by rw [hMd, act hP hpq hG d hd y, hy, mul_zero, zero_smul, add_zero]⟩
  · have hMN : M * (P * diagonal d' * P⁻¹) = 1 := hMd ▸ conj_mul_conj hP d d' hdd
    refine ⟨((d' q - 1) * bJ ε (P *ᵥ Pi.single p 1) (Jm ε *ᵥ y)) * c, ?_⟩
    rw [conjT_eq hM hMN, ← mulVec_mulVec, ← mulVec_mulVec, act hP hpq hG d' hd' (Jm ε *ᵥ y), hc,
      bJ_twist, hy, mul_zero, mul_zero, zero_smul, add_zero, mulVec_add, mulVec_smul, mulVec_smul,
      jm_jm_mulVec, jm_jm_mulVec, smul_smul]

theorem first_flag_space_one_dimensional {a : ℕ} {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (h : 0 < a)
    (hj : j ⟨0, h⟩ = 1) {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {y : Fin n → ℂ} (hy : y ∈ W ⟨1, Nat.succ_lt_succ h⟩) : ∃ t : ℂ, y = t • e := by
  have hr : Module.finrank ℂ (W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have h1 := hW.2.2.1 ⟨0, h⟩
    rw [show (Fin.castSucc ⟨0, h⟩ : Fin (a + 1)) = 0 from Fin.ext rfl, hW.1, finrank_bot, hj] at h1
    exact h1
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : W ⟨1, Nat.succ_lt_succ h⟩)
    (fun h0 => he0 (congrArg Subtype.val h0))).1 hr ⟨y, hy⟩
  exact ⟨t, (congrArg Subtype.val ht).symm⟩

theorem one_le_of_ne {a : ℕ} (i : Fin (a + 1)) (hi : i ≠ 0) : 1 ≤ i.val := by
  rcases Nat.eq_zero_or_pos i.val with h0 | h0
  · exact absurd (Fin.ext (by simp [h0])) hi
  · exact h0

theorem mem_flagM' {a : ℕ} {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (h : 0 < a)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (g : Formalism.REAL.UJ ε)
    (hk : ∀ y, bJ ε e y = 0 → (∃ s : ℂ, uMat g *ᵥ y = y + s • e) ∧ ∃ s : ℂ, (uMat g)ᴴ *ᵥ y = y + s • e) :
    g ∈ flagM ε W := by
  intro i y hy
  have hel : e ∈ W (Fin.last a) := hW.2.1 (Fin.le_last _) he
  have hb : bJ ε e y = 0 := hW.2.2.2 e hel y (hW.2.1 (Fin.le_last i) hy)
  by_cases hi : i = 0
  · subst hi
    rw [hW.1, Submodule.mem_bot] at hy
    subst hy
    simp
  · have hei : e ∈ W i := hW.2.1 (show (⟨1, Nat.succ_lt_succ h⟩ : Fin (a + 1)) ≤ i from
      Fin.le_def.2 (one_le_of_ne i hi)) he
    obtain ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩ := hk y hb
    exact ⟨hs ▸ add_mem hy (Submodule.smul_mem _ s hei), hs' ▸ add_mem hy (Submodule.smul_mem _ s' hei)⟩

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem lie_H {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) :
    P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet ε := by
  refine mem_lie_conj hP _ (fun a b => ?_)
  by_cases h : a = p ∨ a = q ∨ b = p ∨ b = q
  · rw [hG a b h]
    split_ifs with h2
    · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Pi.single_apply, hpq, hpq.symm]
    · simp
  · push_neg at h
    simp [Pi.single_apply, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem lie_algebra_split_torus_generator {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) :
    P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet ε := by
  refine mem_lie_conj hP _ (fun a b => ?_)
  by_cases h : a = p ∨ a = q ∨ b = p ∨ b = q
  · rw [hG a b h]
    split_ifs with h2
    · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Pi.single_apply, hpq, hpq.symm]
    · simp
  · push_neg at h
    simp [Pi.single_apply, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem split_part {a : ℕ} {j : Fin a → ℕ} {W : Flag n a} (h : 0 < a) (hW : IsIsoFlag ε j W)
    (hj : j ⟨0, h⟩ = 1) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (he : P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩) {c : ℂ}
    (hc : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)))
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) (x : ℝ) :
    IsSplit ε W (Pi.single ⟨0, h⟩ x) (expG ε (P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹) x) := by
  have hH := lie_H hP hpq hG
  have hg : uMat (expG ε (P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹) x) =
      P * diagonal (fun a => Complex.exp (x * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a)) * P⁻¹ :=
    toM_expG_conj hP _ hH x
  have hgJ := (expG ε (P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹) x).2
  change (uMat _)ᴴ * Jm ε * uMat _ = Jm ε at hgJ
  have hd : ∀ a, a ≠ p → a ≠ q →
      (fun a => Complex.exp (x * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a)) a = 1 := by
    intro a hap haq; simp [Pi.single_apply, hap, haq]
  have hd' : ∀ a, a ≠ p → a ≠ q →
      (fun a => Complex.exp (-(x * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a))) a = 1 := by
    intro a hap haq; simp [Pi.single_apply, hap, haq]
  have hdd : ∀ a, (fun a => Complex.exp (x * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a)) a *
      (fun a => Complex.exp (-(x * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a))) a = 1 := by
    intro a; simp only; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hk := fun y hy => keep hP hpq hG hc _ _ hd hd' hdd _ hg hgJ y hy
  have hel : P *ᵥ Pi.single p 1 ∈ W (Fin.last a) := hW.2.1 (Fin.le_last _) he
  refine ⟨mem_flagM' hW h he _ hk, ?_, ?_⟩
  · intro i y hy
    by_cases hi : i = ⟨0, h⟩
    · subst hi
      obtain ⟨t, rfl⟩ := first_flag_space_one_dimensional hW h hj he (col_ne_zero hP p) hy
      rw [Pi.single_eq_same, mulVec_smul, hg, act_col hP]
      have h1 : Complex.exp (x * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) p) =
          ((Real.exp x : ℝ) : ℂ) := by simp [Pi.single_apply, hpq, Complex.ofReal_exp]
      rw [h1, smul_comm, sub_self]
      exact zero_mem _
    · rw [Pi.single_eq_of_ne hi, Real.exp_zero, Complex.ofReal_one, one_smul]
      have hb : bJ ε (P *ᵥ Pi.single p 1) y = 0 :=
        hW.2.2.2 _ hel y (hW.2.1 (Fin.le_last _) hy)
      obtain ⟨s, hs⟩ := (hk y hb).1
      rw [hs, add_sub_cancel_left]
      have hle : (⟨1, Nat.succ_lt_succ h⟩ : Fin (a + 1)) ≤ i.castSucc :=
        Fin.le_def.2 (by rw [Fin.coe_castSucc]; exact Nat.one_le_iff_ne_zero.2 (fun h0 => hi (Fin.ext h0)))
      exact Submodule.smul_mem _ s (hW.2.1 hle he)
  · intro y hy
    obtain ⟨s, hs⟩ := (hk y (hy _ hel)).1
    rw [hs, add_sub_cancel_left]
    exact Submodule.smul_mem _ s hel

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem mat_ext {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ y, A *ᵥ y = B *ᵥ y) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun y => by simpa [Matrix.toLin'_apply] using h y)

theorem bJ_swap (u : Fin n → ℂ) : bJ ε (Jm ε *ᵥ u) u = bJ ε u (Jm ε *ᵥ u) := by
  rw [bJ, bJ, star_mulVec, jm_conjTranspose, ← dotProduct_mulVec]

theorem bJ_twist2 (c : ℂ) (e y : Fin n → ℂ) :
    bJ ε (c • (Jm ε *ᵥ e)) y = star c * bJ ε e (Jm ε *ᵥ y) := by
  have := bJ_twist (ε := ε) c e (Jm ε *ᵥ y)
  rwa [jm_jm_mulVec] at this

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

theorem bJ_pq : bJ ε (P *ᵥ Pi.single p 1) (P *ᵥ Pi.single q 1) = 1 := by
  rw [coord hP p, row_p hpq hG, mulVec_mulVec, nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP),
    one_mulVec]
  simp

theorem bJ_qp : bJ ε (P *ᵥ Pi.single q 1) (P *ᵥ Pi.single p 1) = 1 := by
  rw [coord hP q, row_q hpq hG, mulVec_mulVec, nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP),
    one_mulVec]
  simp

theorem c_real {c : ℂ} (hc : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1))) : star c = c := by
  have h1 := bJ_pq hP hpq hG
  have h2 := bJ_qp hP hpq hG
  rw [hc, bJ_smul_right] at h1
  rw [hc, bJ_smul_left, bJ_swap] at h2
  have hs : bJ ε (P *ᵥ Pi.single p 1) (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ hs (h2.trans h1.symm)

theorem comm_J {c : ℂ} (hc : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)))
    (d : Fin n → ℂ) (l : ℂ) (hdp : d p = l) (hdq : d q = l) (hd : ∀ a, a ≠ p → a ≠ q → d a = 1) :
    (P * diagonal d * P⁻¹) * Jm ε = Jm ε * (P * diagonal d * P⁻¹) := by
  have hcr := c_real hP hpq hG hc
  refine mat_ext fun y => ?_
  have e1 : ((P * diagonal d * P⁻¹) * Jm ε) *ᵥ y = (P * diagonal d * P⁻¹) *ᵥ (Jm ε *ᵥ y) := by
    rw [mulVec_mulVec]
  have e2 : (Jm ε * (P * diagonal d * P⁻¹)) *ᵥ y = Jm ε *ᵥ ((P * diagonal d * P⁻¹) *ᵥ y) := by
    rw [mulVec_mulVec]
  rw [e1, e2, act hP hpq hG d hd, act hP hpq hG d hd, hdp, hdq, hc,
    bJ_twist, bJ_twist2, hcr]
  simp only [mulVec_add, mulVec_smul, jm_jm_mulVec]
  module

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem bJ_transfer {M K : Matrix (Fin n) (Fin n) ℂ} (hJM : Jm ε * M = Kᴴ * Jm ε) (u y : Fin n → ℂ) :
    bJ ε u (M *ᵥ y) = bJ ε (K *ᵥ u) y := by
  rw [bJ, bJ, mulVec_mulVec, hJM, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem jm_swap {M K : Matrix (Fin n) (Fin n) ℂ} (hK : Kᴴ * Jm ε * K = Jm ε) (hKM : K * M = 1) :
    Jm ε * M = Kᴴ * Jm ε := by
  calc Jm ε * M = Kᴴ * Jm ε * K * M := by rw [hK]
    _ = Kᴴ * Jm ε * (K * M) := by simp only [Matrix.mul_assoc]
    _ = Kᴴ * Jm ε := by rw [hKM, Matrix.mul_one]

theorem uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

theorem central {a : ℕ} {j : Fin a → ℕ} {W : Flag n a} (h : 0 < a) (hW : IsIsoFlag ε j W)
    (hj : j ⟨0, h⟩ = 1) (he : P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩) {c : ℂ}
    (hc : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)))
    (d : Fin n → ℂ) (l : ℂ) (hdp : d p = l) (hdq : d q = l) (hd : ∀ a, a ≠ p → a ≠ q → d a = 1)
    (g : Formalism.REAL.UJ ε) (hg : uMat g = P * diagonal d * P⁻¹) (m : Formalism.REAL.UJ ε) (hm : m ∈ leviOne ε W) :
    g * m = m * g := by
  have hmF : m ∈ flagM ε W := hm.1
  have hkF : m⁻¹ ∈ flagM ε W := ((leviOne ε W).inv_mem hm).1
  have hMK : uMat m * uMat m⁻¹ = 1 := by rw [← uMat_mul', mul_inv_cancel]; rfl
  have hKM : uMat m⁻¹ * uMat m = 1 := by rw [← uMat_mul', inv_mul_cancel]; rfl
  have hMJ : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
  have hKJ : (uMat m⁻¹)ᴴ * Jm ε * uMat m⁻¹ = Jm ε := (m⁻¹).2
  have hJM := jm_swap hKJ hKM
  have hJK := jm_swap hMJ hMK
  have he0 := col_ne_zero hP p
  obtain ⟨μ, hμ⟩ := first_flag_space_one_dimensional hW h hj he he0 (hmF _ _ he).1
  obtain ⟨ν, hν⟩ := first_flag_space_one_dimensional hW h hj he he0 (hmF _ _ he).2
  obtain ⟨κ, hκ⟩ := first_flag_space_one_dimensional hW h hj he he0 (hkF _ _ he).1
  obtain ⟨ρ, hρ⟩ := first_flag_space_one_dimensional hW h hj he he0 (hkF _ _ he).2
  have hKe' : uMat m⁻¹ *ᵥ (P *ᵥ Pi.single q 1) = ν • (P *ᵥ Pi.single q 1) := by
    have e1 : uMat m⁻¹ *ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) =
        Jm ε *ᵥ ((Jm ε * uMat m⁻¹) *ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single p 1))) := by
      rw [← mulVec_mulVec, jm_jm_mulVec]
    rw [hc, mulVec_smul, e1, hJK, ← mulVec_mulVec, jm_jm_mulVec, hν, mulVec_smul, smul_comm]
  have hMe' : uMat m *ᵥ (P *ᵥ Pi.single q 1) = ρ • (P *ᵥ Pi.single q 1) := by
    have e1 : uMat m *ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) =
        Jm ε *ᵥ ((Jm ε * uMat m) *ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single p 1))) := by
      rw [← mulVec_mulVec, jm_jm_mulVec]
    rw [hc, mulVec_smul, e1, hJM, ← mulVec_mulVec, jm_jm_mulVec, hρ, mulVec_smul, smul_comm]
  have hμν : μ = star ν := by
    have h1 := bJ_transfer hJM (P *ᵥ Pi.single q 1) (P *ᵥ Pi.single p 1)
    rw [hμ, hKe', bJ_smul_right, bJ_smul_left, bJ_qp hP hpq hG] at h1
    simpa using h1
  have hρκ : ρ = star κ := by
    have h1 := bJ_transfer hJM (P *ᵥ Pi.single p 1) (P *ᵥ Pi.single q 1)
    rw [hMe', hκ, bJ_smul_right, bJ_smul_left, bJ_pq hP hpq hG] at h1
    simpa using h1
  refine Subtype.ext (Units.ext ?_)
  show uMat g * uMat m = uMat m * uMat g
  refine mat_ext fun y => ?_
  have e1 : (uMat g * uMat m) *ᵥ y = uMat g *ᵥ (uMat m *ᵥ y) := by rw [mulVec_mulVec]
  have e2 : (uMat m * uMat g) *ᵥ y = uMat m *ᵥ (uMat g *ᵥ y) := by rw [mulVec_mulVec]
  rw [e1, e2, hg, act hP hpq hG d hd, act hP hpq hG d hd, hdp, hdq, bJ_transfer hJM, bJ_transfer hJM,
    hKe', hκ, bJ_smul_left, bJ_smul_left]
  simp only [mulVec_add, mulVec_smul, hμ, hMe', hμν, hρκ]
  module

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

theorem circle_part {a : ℕ} {j : Fin a → ℕ} {W : Flag n a} (h : 0 < a) (hW : IsIsoFlag ε j W)
    (hj : j ⟨0, h⟩ = 1) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (he : P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩) {c : ℂ}
    (hc : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)))
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) (θ : ℝ) :
    expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ ∈ KG ε ⊓ leviOne ε W ∧
      ∀ m ∈ leviOne ε W, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ * m =
        m * expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ := by
  have hT := lie_algebra_split_torus_generator hP hpq hG
  have hg : uMat (expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ) =
      P * diagonal (fun a => Complex.exp (θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a))
        * P⁻¹ := toM_expG_conj hP _ hT θ
  have hgJ := (expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ).2
  change (uMat _)ᴴ * Jm ε * uMat _ = Jm ε at hgJ
  have hdp : (fun a => Complex.exp (θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a)) p =
      Complex.exp (θ * Complex.I) := by simp [Pi.single_apply, hpq]
  have hdq : (fun a => Complex.exp (θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a)) q =
      Complex.exp (θ * Complex.I) := by simp [Pi.single_apply, hpq.symm]
  have hd : ∀ a, a ≠ p → a ≠ q →
      (fun a => Complex.exp (θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a)) a = 1 := by
    intro a hap haq; simp [Pi.single_apply, hap, haq]
  have hd' : ∀ a, a ≠ p → a ≠ q →
      (fun a => Complex.exp (-(θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a))) a = 1 := by
    intro a hap haq; simp [Pi.single_apply, hap, haq]
  have hdd : ∀ a, (fun a => Complex.exp (θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a)) a *
      (fun a => Complex.exp (-(θ * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) a))) a = 1 := by
    intro a; simp only; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcomm := comm_J hP hpq hG hc _ _ hdp hdq hd
  rw [← hg] at hcomm
  have hunit : (uMat (expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ))ᴴ *
      uMat (expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ) = 1 := by
    set M := uMat (expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ)
    calc Mᴴ * M = Mᴴ * (Jm ε * Jm ε) * M := by rw [jm_mul_self, Matrix.mul_one]
      _ = Mᴴ * Jm ε * (Jm ε * M) := by simp only [Matrix.mul_assoc]
      _ = Mᴴ * Jm ε * M * Jm ε := by rw [← hcomm]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgJ, jm_mul_self]
  have hflag := mem_flagM' hW h he _ (fun y hy => keep hP hpq hG hc _ _ hd hd' hdd _ hg hgJ y hy)
  refine ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, fun m hm => central hP hpq hG h hW hj he hc _ _ hdp hdq hd _ hg m hm⟩
  · show toM _ ∈ Kset ε
    exact ⟨Matrix.mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact hunit), hcomm⟩
  · exact ⟨hflag, fun i => GlobalTheory.IwDelta.detOn_eq_one ⟨hunit, hflag⟩ i⟩

end GlobalTheory.SplitTorus

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

theorem GlobalTheory.SplitTorus.split_torus_circle : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ ∈ lieSet ε ∧ (∀ x : ℝ, IsSplit ε W (Pi.single ⟨0, h⟩ x) (expG ε (P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹) x)) ∧ P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ ∈ lieSet ε ∧ ∀ θ : ℝ, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ ∈ KG ε ⊓ leviOne ε W ∧ ∀ m ∈ leviOne ε W, expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ * m = m * expG ε (P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹) θ := by
  intro n ε a j W h hW hj P p q c hP hpq he hc hG
  exact ⟨GlobalTheory.SplitTorus.lie_H hP hpq hG, GlobalTheory.SplitTorus.split_part h hW hj hP hpq he hc hG,
    GlobalTheory.SplitTorus.lie_algebra_split_torus_generator hP hpq hG, fun θ => GlobalTheory.SplitTorus.circle_part h hW hj hP hpq he hc hG θ⟩
