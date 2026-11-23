import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.UnipRadUnit

variable {n : ℕ}

def RadCond (ε : Fin n → Bool) (e : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Y *ᵥ e = 0 ∧ (∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = 0 → ∃ c : ℂ, Y *ᵥ y = c • e) ∧
    ∀ y, star e ⬝ᵥ (Jm ε *ᵥ (Y *ᵥ y)) = 0

theorem RadCond.add {ε : Fin n → Bool} {e : Fin n → ℂ} {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (h' : RadCond ε e Y') : RadCond ε e (Y + Y') := by
  refine ⟨by rw [add_mulVec, h.1, h'.1, add_zero], fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 y hy
    obtain ⟨c', hc'⟩ := h'.2.1 y hy
    exact ⟨c + c', by rw [add_mulVec, hc, hc', add_smul]⟩
  · rw [add_mulVec, mulVec_add, dotProduct_add, h.2.2, h'.2.2, add_zero]

theorem RadCond.smul {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (s : ℂ) : RadCond ε e (s • Y) := by
  refine ⟨by rw [Matrix.smul_mulVec, h.1, smul_zero], fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 y hy
    exact ⟨s * c, by rw [Matrix.smul_mulVec, hc, smul_smul]⟩
  · rw [Matrix.smul_mulVec, mulVec_smul, dotProduct_smul, h.2.2, smul_zero]

theorem RadCond.neg {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) : RadCond ε e (-Y) := by
  simpa using h.smul (-1)

theorem RadCond.sub {ε : Fin n → Bool} {e : Fin n → ℂ} {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (h' : RadCond ε e Y') : RadCond ε e (Y - Y') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem RadCond.pow_three {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) : Y ^ 3 = 0 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  obtain ⟨c, hc⟩ := h.2.1 (Y *ᵥ Pi.single i 1) (h.2.2 _)
  rw [zero_mulVec, pow_succ, pow_two, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_smul, h.1, smul_zero]

theorem RadCond.exp_mulVec {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (y : Fin n → ℂ) (hy : star e ⬝ᵥ (Jm ε *ᵥ y) = 0) :
    NormedSpace.exp Y *ᵥ y = y + Y *ᵥ y := by
  have h3 := h.pow_three
  have hexp : NormedSpace.exp Y = ∑ k ∈ Finset.range 3, ((k.factorial : ℂ)⁻¹) • Y ^ k := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    refine tsum_eq_sum fun k hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    rw [← Nat.add_sub_cancel' hk, pow_add, h3, zero_mul, smul_zero]
  obtain ⟨c, hc⟩ := h.2.1 y hy
  have h2 : Y *ᵥ (Y *ᵥ y) = 0 := by rw [hc, mulVec_smul, h.1, smul_zero]
  rw [hexp]
  simp [Finset.sum_range_succ, add_mulVec, Matrix.smul_mulVec, pow_two, ← mulVec_mulVec, h2]

theorem expG_mem_flagN {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : 0 < a) (hW : IsIsoFlag ε j W) (hj : j ⟨0, h⟩ = 1)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieSet ε) (hR : RadCond ε e Y) (t : ℝ) :
    expG ε Y t ∈ flagN ε W := by
  obtain ⟨hW0, hmono, hrank, hiso⟩ := hW
  have hrank1 : Module.finrank ℂ (W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have h1 := hrank ⟨0, h⟩
    have hc : (⟨0, h⟩ : Fin a).castSucc = 0 := Fin.ext rfl
    rw [hc, hW0, finrank_bot, hj, zero_add] at h1
    exact h1
  have hspan : ∀ y ∈ W ⟨1, Nat.succ_lt_succ h⟩, ∃ d : ℂ, y = d • e := by
    intro y hy
    have he0' : (⟨e, he⟩ : W ⟨1, Nat.succ_lt_succ h⟩) ≠ 0 := fun h0 => he0 (congrArg Subtype.val h0)
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp hrank1 ⟨y, hy⟩
    exact ⟨d, (congrArg Subtype.val hd).symm⟩
  have hlast : W ⟨1, Nat.succ_lt_succ h⟩ ≤ W (Fin.last a) := hmono (Fin.le_last _)
  have hperp : ∀ y ∈ W (Fin.last a), star e ⬝ᵥ (Jm ε *ᵥ y) = 0 := fun y hy => hiso e (hlast he) y hy
  have hRZ := hR.smul (t : ℂ)
  have hexp : uMat (expG ε Y t) = NormedSpace.exp ((t : ℂ) • Y) := toM_expG ε Y t hY
  have key : ∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = 0 → ∃ c : ℂ, uMat (expG ε Y t) *ᵥ y - y = c • e := by
    intro y hy
    rw [hexp, hRZ.exp_mulVec y hy, add_sub_cancel_left]
    exact hRZ.2.1 y hy
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · have hy' := hperp y (hmono (Fin.le_last _) hy)
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · have hi' : i.succ = ⟨1, Nat.succ_lt_succ h⟩ := Fin.ext (by simp [hi])
      rw [hi'] at hy
      obtain ⟨d, rfl⟩ := hspan y hy
      rw [hexp, hRZ.exp_mulVec _ hy', add_sub_cancel_left, mulVec_smul, hRZ.1, smul_zero]
      exact zero_mem _
    · obtain ⟨c, hc⟩ := key y hy'
      rw [hc]
      have hle : (⟨1, Nat.succ_lt_succ h⟩ : Fin (a + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simp; omega
      exact hmono hle (Submodule.smul_mem _ c he)
  · obtain ⟨c, hc⟩ := key y (hy e (hlast he))
    rw [hc]
    exact hlast (Submodule.smul_mem _ c he)

def theta (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Zᴴ * Jm ε)

theorem Jm_Jm_mul (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem re_mem (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (2⁻¹ : ℂ) • (Z + theta ε Z) ∈ lieSet ε := by
  show ((2⁻¹ : ℂ) • (Z + theta ε Z))ᴴ * Jm ε + Jm ε * ((2⁻¹ : ℂ) • (Z + theta ε Z)) = 0
  simp only [theta, conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_mul,
    Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Jm_Jm_mul]
  simp

theorem im_mem (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Complex.I / 2) • (theta ε Z - Z) ∈ lieSet ε := by
  show ((Complex.I / 2) • (theta ε Z - Z))ᴴ * Jm ε + Jm ε * ((Complex.I / 2) • (theta ε Z - Z)) = 0
  simp only [theta, conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul,
    Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Jm_Jm_mul]
  simp
  module

theorem decomp {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : 0 < a) (hW : IsIsoFlag ε j W) (hj : j ⟨0, h⟩ = 1)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : RadCond ε e Z) (hθ : RadCond ε e (theta ε Z)) :
    ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧
      (∀ t, expG ε X' t ∈ flagN ε W) ∧ Z = X + Complex.I • X' := by
  refine ⟨(2⁻¹ : ℂ) • (Z + theta ε Z), (Complex.I / 2) • (theta ε Z - Z), re_mem ε Z, im_mem ε Z,
    expG_mem_flagN h hW hj he he0 (re_mem ε Z) ((hZ.add hθ).smul _),
    expG_mem_flagN h hW hj he he0 (im_mem ε Z) ((hθ.sub hZ).smul _), ?_⟩
  rw [smul_smul, show Complex.I * (Complex.I / 2) = -2⁻¹ by rw [← mul_div_assoc, Complex.I_mul_I]; ring]
  module

theorem vecMulVec_mulVec' (x φ y : Fin n → ℂ) : vecMulVec x φ *ᵥ y = (φ ⬝ᵥ y) • x := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem theta_vecMulVec (ε : Fin n → Bool) (x φ : Fin n → ℂ) :
    theta ε (vecMulVec x φ) = -vecMulVec (Jm ε *ᵥ star φ) (star x ᵥ* Jm ε) := by
  rw [theta, conjTranspose_vecMulVec, mul_vecMulVec, vecMulVec_mul]

theorem radCond_col {ε : Fin n → Bool} {e : Fin n → ℂ} (hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0)
    (φ : Fin n → ℂ) (hφ : φ ⬝ᵥ e = 0) : RadCond ε e (vecMulVec e φ) := by
  refine ⟨by rw [vecMulVec_mulVec', hφ, zero_smul], fun y _ => ⟨φ ⬝ᵥ y, vecMulVec_mulVec' _ _ _⟩,
    fun y => ?_⟩
  rw [vecMulVec_mulVec', mulVec_smul, dotProduct_smul, hfe, smul_zero]

theorem radCond_row {ε : Fin n → Bool} {e : Fin n → ℂ} (hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0)
    (x : Fin n → ℂ) (hx : star e ⬝ᵥ (Jm ε *ᵥ x) = 0) :
    RadCond ε e (vecMulVec x (star e ᵥ* Jm ε)) := by
  refine ⟨by rw [vecMulVec_mulVec', ← dotProduct_mulVec, hfe, zero_smul], fun y hy => ⟨0, ?_⟩, fun y => ?_⟩
  · rw [vecMulVec_mulVec', ← dotProduct_mulVec, hy, zero_smul, zero_smul]
  · rw [vecMulVec_mulVec', mulVec_smul, dotProduct_smul, hx, smul_zero]

theorem single_eq_vecMulVec (p b : Fin n) :
    Matrix.single p b (1 : ℂ) = vecMulVec (Pi.single p 1) (Pi.single b 1) := by
  ext i k
  rcases eq_or_ne p i with rfl | hi
  · rcases eq_or_ne b k with rfl | hk
    · simp [vecMulVec_apply, Matrix.single_apply]
    · simp [vecMulVec_apply, Matrix.single_apply, hk, hk.symm]
  · simp [vecMulVec_apply, Matrix.single_apply, hi, hi.symm]

theorem matrixUnits_mem_radical : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → (∀ b, b ≠ p → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single p b 1 * P⁻¹ = X + Complex.I • X') ∧ ∀ b, b ≠ q → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single b q 1 * P⁻¹ = X + Complex.I • X' := by
  intro n ε a j W h hW hj P p q c hP hpq hp hq hG
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  set e := P *ᵥ Pi.single p 1 with he_def
  have hPe : P⁻¹ *ᵥ e = Pi.single p 1 := by rw [he_def, mulVec_mulVec, hPP, one_mulVec]
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := congrFun hPe p
    rw [h0, mulVec_zero] at h1
    simp at h1
  have hGp : ∀ k, (Pᴴ * Jm ε * P) p k = if k = q then 1 else 0 := by
    intro k
    rw [hG p k (Or.inl rfl)]
    by_cases hk : k = q <;> simp [hk, hpq]
  have hf : ∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = (P⁻¹ *ᵥ y) q := by
    intro y
    have hy : y = P *ᵥ (P⁻¹ *ᵥ y) := by rw [mulVec_mulVec, hPP', one_mulVec]
    conv_lhs => rw [hy]
    rw [he_def, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    generalize P⁻¹ *ᵥ y = v
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hGp]
  have hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0 := by
    rw [hf, hPe]; simp [hpq.symm]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hZ : P * Matrix.single p b 1 * P⁻¹ = vecMulVec e (Pi.single b 1 ᵥ* P⁻¹) := by
      rw [single_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul]
    have hre : (Pi.single b 1 ᵥ* P⁻¹) ⬝ᵥ e = 0 := by
      rw [← dotProduct_mulVec, hPe]; simp [hb]
    have h1 := radCond_col hfe _ hre
    have h2 : RadCond ε e (theta ε (vecMulVec e (Pi.single b 1 ᵥ* P⁻¹))) := by
      rw [theta_vecMulVec]
      refine (radCond_row hfe _ ?_).neg
      rw [mulVec_mulVec, Jm_mul_self, one_mulVec, star_dotProduct, star_star, hre, star_zero]
    rw [hZ]
    exact decomp h hW hj hp he0 h1 h2
  · have hZ : P * Matrix.single b q 1 * P⁻¹ = vecMulVec (P *ᵥ Pi.single b 1) (Pi.single q 1 ᵥ* P⁻¹) := by
      rw [single_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul]
    have hs : Pi.single q 1 ᵥ* P⁻¹ = star e ᵥ* Jm ε := by
      funext k
      have h1 := hf (Pi.single k 1)
      rw [dotProduct_mulVec] at h1
      simpa [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.single_apply] using h1.symm
    have hv : star e ⬝ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single b 1)) = 0 := by
      rw [hf, mulVec_mulVec, hPP, one_mulVec]; simp [hb]
    have h1 := radCond_row hfe _ hv
    have h2 : RadCond ε e (theta ε (vecMulVec (P *ᵥ Pi.single b 1) (star e ᵥ* Jm ε))) := by
      rw [theta_vecMulVec, star_vecMul, Jm_conjTranspose, star_star, mulVec_mulVec, Jm_mul_self, one_mulVec]
      refine (radCond_col hfe _ ?_).neg
      rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, Jm_conjTranspose, ← dotProduct_mulVec, hv,
        star_zero]
    rw [hZ, hs]
    exact decomp h hW hj hp he0 h1 h2

end GlobalTheory.UnipRadUnit
