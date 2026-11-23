import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCellDens

theorem telesc (s : ℕ) (Δ : ℕ → ℝ) (h0 : Δ 0 = 1) (hp : ∀ k, k ≤ s → Δ k ≠ 0) :
    ∏ i ∈ Finset.range s, (Δ (i + 1) / Δ i) ^ (s - i) = ∏ i ∈ Finset.range s, Δ (i + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih' := ih fun k hk => hp k (by omega)
    have e1 : ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) ^ (s + 1 - i) =
        (∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) ^ (s - i)) *
          ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show s + 1 - i = (s - i) + 1 by omega, pow_succ]
    have e2 : ∏ i ∈ Finset.range (s + 1), (Δ (i + 1) / Δ i) = Δ (s + 1) := by
      rw [Finset.prod_div_distrib]
      have a1 := Finset.prod_range_succ' Δ (s + 1)
      have a2 := Finset.prod_range_succ Δ (s + 1)
      have hne : ∏ i ∈ Finset.range (s + 1), Δ i ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i hi => hp i (by rw [Finset.mem_range] at hi; omega)
      rw [h0, mul_one] at a1
      rw [a1] at a2
      field_simp
      linarith [a2]
    rw [e1, e2, Finset.prod_range_succ, ih', Nat.sub_self, pow_zero, mul_one, Finset.prod_range_succ]

theorem key (s : ℕ) (Δ : ℕ → ℝ) (h0 : Δ 0 = 1) (hp : ∀ k, k ≤ s → 0 < Δ k) :
    ∏ i : Fin s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) =
      Δ s ^ ((s : ℤ) - 1) * ∏ i : Fin s, Δ i ^ (-2 : ℤ) := by
  have hne : ∀ k, k ≤ s → Δ k ≠ 0 := fun k hk => (hp k hk).ne'
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) s,
    Fin.prod_univ_eq_prod_range (fun i : ℕ => Δ i ^ (-2 : ℤ)) s]
  have e1 : ∏ i ∈ Finset.range s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ ((s - 1 - i : ℕ) + 1)) =
      ∏ i ∈ Finset.range s, (Δ s / Δ i / (Δ (i + 1) / Δ i) ^ (s - i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show s - 1 - i + 1 = s - i by omega]
  rw [e1, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    telesc s Δ h0 hne, Finset.prod_zpow]
  have a1 := Finset.prod_range_succ' Δ s
  have a2 := Finset.prod_range_succ Δ s
  rw [h0, mul_one] at a1
  rw [a1] at a2
  rw [a2]
  have hP : ∏ i ∈ Finset.range s, Δ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => hne i (by rw [Finset.mem_range] at hi; omega)
  have hs := hne s le_rfl
  rw [zpow_sub₀ hs, zpow_natCast, zpow_one, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
  field_simp

end GlobalTheory.FlagCellDens

namespace GlobalTheory.FlagCellDens

theorem leadMinor_pos {s : ℕ} {M : Matrix (Fin s) (Fin s) ℂ} (hM : M.PosDef) (k : ℕ) :
    0 < (leadMinor M k).re ∧ (leadMinor M k).im = 0 := by
  have h := (hM.submatrix (e := (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)) Subtype.val_injective).det_pos
  have := Complex.pos_iff.1 h
  exact ⟨this.1, this.2.symm⟩

theorem leadMinor_self {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) : leadMinor M s = M.det := by
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin s => (a : ℕ) < s)
    fun a => a.2) M
  exact this

def lowEquiv {s k : ℕ} (hk : k ≤ s) : Fin k ≃ {a : Fin s // (a : ℕ) < k} where
  toFun j := ⟨Fin.castLE hk j, j.2⟩
  invFun a := ⟨a.1.1, a.2⟩
  left_inv j := rfl
  right_inv a := rfl

theorem lminor_transpose {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i : Fin (s + 1)) :
    ReciprocityTheory.ChartRestriction.G.FD.lminor Mᵀ i = leadMinor M i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor leadMinor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have := Matrix.det_submatrix_equiv_self (lowEquiv (Nat.le_of_lt_succ i.isLt))
    (M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < i} → Fin s) Subtype.val)
  rw [← this, Matrix.submatrix_submatrix]
  rfl

end GlobalTheory.FlagCellDens

open GlobalTheory.FlagCellDens in

theorem GlobalTheory.FlagCellDens.main : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ), ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ) * (G.det.re / (leadMinor (upU y * G * (upU y)ᴴ) i).re / grD (upU y * G * (upU y)ᴴ) i ^ ((s - 1 - i : ℕ) + 1))) = GlobalTheory.TrueCx.flagConst s * G.det.re ^ ((s : ℤ) - 1) * GlobalTheory.FlagFibre.dens Gᵀ y := by
  intro s G hG y
  set M := upU y * G * (upU y)ᴴ with hMdef
  have hU : (upU y).det = 1 := by rw [upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  have hM : M.PosDef := hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [hU]; exact isUnit_one)))
  have hdet : M.det = G.det := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hU]; simp
  have hT : (GlobalTheory.FlagFibre.uni y)ᴴ * Gᵀ * GlobalTheory.FlagFibre.uni y = Mᵀ := by
    rw [hMdef, upU_eq]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    congr 1
  set Δ : ℕ → ℝ := fun k => (leadMinor M k).re with hΔ
  have hGs : G.det.re = Δ s := by rw [hΔ]; simp only [leadMinor_self, hdet]
  have hnorm : ∀ i : Fin s, ‖ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni y)ᴴ * Gᵀ * GlobalTheory.FlagFibre.uni y) i.castSucc‖ = Δ i := by
    intro i
    rw [hT, lminor_transpose]
    obtain ⟨h1, h2⟩ := leadMinor_pos hM i
    have : leadMinor M (i.castSucc : ℕ) = ((leadMinor M i).re : ℂ) := Complex.ext (by simp) (by simp [h2])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
  have h0 : Δ 0 = 1 := by
    simp only [hΔ, leadMinor]
    haveI : IsEmpty {a : Fin s // (a : ℕ) < 0} := ⟨fun a => Nat.not_lt_zero _ a.2⟩
    rw [Matrix.det_isEmpty]; simp
  have hp : ∀ k, k ≤ s → 0 < Δ k := fun k _ => (leadMinor_pos hM k).1
  rw [Finset.prod_mul_distrib, GlobalTheory.FlagFibre.dens]
  simp only [hnorm]
  have hc : ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ)) = GlobalTheory.TrueCx.flagConst s := by
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ))) s,
      Finset.prod_range_reflect (fun i : ℕ => ((i.factorial : ℝ) / Real.pi ^ i)) s]
    rfl
  rw [hc, mul_assoc]
  congr 1
  rw [hGs]
  exact key s Δ h0 hp
