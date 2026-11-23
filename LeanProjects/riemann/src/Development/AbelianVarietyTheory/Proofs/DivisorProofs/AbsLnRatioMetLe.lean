import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GradedCompare

open Matrix GlobalTheory.GradedNorm GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder

variable {n : ℕ}

def Cmp (m : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (((m : ℂ) • B) - A).PosSemidef ∧ (((m : ℂ) • A) - B).PosSemidef

theorem Cmp.symm {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) : Cmp m B A := ⟨h.2, h.1⟩

theorem psd_of_quad {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ A *ᵥ v).re ≤ m * (star v ⬝ᵥ B *ᵥ v).re) :
    (((m : ℂ) • B) - A).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  have hH : ((m : ℂ) • B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, hB.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
  refine ⟨hH.sub hA.isHermitian, fun v => ?_⟩
  have ha := Complex.nonneg_iff.1 (hA.posSemidef.dotProduct_mulVec_nonneg v)
  have hb := Complex.nonneg_iff.1 (hB.posSemidef.dotProduct_mulVec_nonneg v)
  have e : star v ⬝ᵥ (((m : ℂ) • B) - A) *ᵥ v = (m : ℂ) * (star v ⬝ᵥ B *ᵥ v) - star v ⬝ᵥ A *ᵥ v := by
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith [h v]
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, ← ha.2, ← hb.2,
      mul_zero, sub_zero]

theorem Cmp.mix {m s : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hm : 1 ≤ m)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : Cmp m A (mix s A B) := by
  have h0 : (0 : ℂ) ≤ (((1 - s) * (m - 1) : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hm))
  have h1 : (0 : ℂ) ≤ ((s : ℝ) : ℂ) := Complex.zero_le_real.2 hs.1
  constructor
  · have e : ((m : ℂ) • GradedNorm.mix s A B) - A =
        (((1 - s) * (m - 1) : ℝ) : ℂ) • A + ((s : ℝ) : ℂ) • (((m : ℂ) • B) - A) := by
      ext i j
      simp only [GradedNorm.mix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact (hA.posSemidef.smul h0).add (h.1.smul h1)
  · have e : ((m : ℂ) • A) - GradedNorm.mix s A B =
        (((1 - s) * (m - 1) : ℝ) : ℂ) • A + ((s : ℝ) : ℂ) • (((m : ℂ) • A) - B) := by
      ext i j
      simp only [GradedNorm.mix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact (hA.posSemidef.smul h0).add (h.2.smul h1)

theorem Cmp.inv {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hB : B.PosDef) (hm : 0 < m) :
    Cmp m A⁻¹ B⁻¹ :=
  ⟨GlobalTheory.CompMetric.inv_sub_posSemidef hm hB hA h.2, GlobalTheory.CompMetric.inv_sub_posSemidef hm hA hB h.1⟩

theorem Cmp.transpose {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) : Cmp m Aᵀ Bᵀ := by
  refine ⟨?_, ?_⟩
  · have := h.1.transpose
    rwa [transpose_sub, transpose_smul] at this
  · have := h.2.transpose
    rwa [transpose_sub, transpose_smul] at this

theorem Cmp.dual {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hB : B.PosDef) (hm : 0 < m) :
    Cmp m (dualGram A) (dualGram B) :=
  (h.inv hA hB hm).transpose

theorem Cmp.mixDual {m s : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hB : B.PosDef)
    (hm : 1 ≤ m) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Cmp m A (GradedNorm.mixDual s A B) := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have h1 := (h.dual hA hB hm0).mix (dualGram_posDef hA) hm hs
  have h2 := h1.dual (dualGram_posDef hA) (mix_posDef hs (dualGram_posDef hA) (dualGram_posDef hB)) hm0
  rwa [dualGram_dualGram ((isUnit_iff_isUnit_det _).1 hA.isUnit)] at h2

theorem lminor_eq (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin (n + 1)) :
    lminor M k = ((of fun (a : Fin n) (b : Fin k) => if a = Fin.castLE (Nat.le_of_lt_succ k.2) b then (1 : ℂ) else 0)ᴴ * M *
      of fun (a : Fin n) (b : Fin k) => if a = Fin.castLE (Nat.le_of_lt_succ k.2) b then (1 : ℂ) else 0).det := by
  unfold lminor
  congr 1
  ext i j
  simp [mul_apply, conjTranspose_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem Cmp.lminor_le {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hm : 0 ≤ m)
    (k : Fin (n + 1)) : (lminor A k).re ≤ m ^ (k : ℕ) * (lminor B k).re := by
  rw [lminor_eq, lminor_eq]
  exact GlobalTheory.CompMetric.det_re_le_of_sub hm hA h.1 _

theorem lminor_re_pos {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosDef) (k : Fin (n + 1)) :
    0 < (lminor M k).re ∧ ((lminor M k).re : ℂ) = lminor M k := by
  have := Complex.pos_iff.1 (lminor_pos h k)
  exact ⟨this.1, Complex.ext (by simp) (by simp [this.2])⟩

theorem grSq_eq {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosDef) (i : Fin n) :
    grSq M i = (lminor M i.succ).re / (lminor M i.castSucc).re := by
  rw [grSq, ← (lminor_re_pos h i.succ).2, ← (lminor_re_pos h i.castSucc).2, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

theorem Cmp.abs_log_lminor {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hB : B.PosDef)
    (hm : 1 ≤ m) (k : Fin (n + 1)) :
    |Real.log (lminor A k).re - Real.log (lminor B k).re| ≤ (k : ℕ) * Real.log m := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have pa := (lminor_re_pos hA k).1
  have pb := (lminor_re_pos hB k).1
  have hp : 0 < m ^ (k : ℕ) := pow_pos hm0 _
  have l1 := Real.log_le_log pa (h.lminor_le hA hm0.le k)
  have l2 := Real.log_le_log pb (h.symm.lminor_le hB hm0.le k)
  rw [Real.log_mul hp.ne' pb.ne', Real.log_pow] at l1
  rw [Real.log_mul hp.ne' pa.ne', Real.log_pow] at l2
  rw [abs_le]
  constructor <;> linarith

theorem Cmp.abs_log_grSq {m : ℝ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Cmp m A B) (hA : A.PosDef) (hB : B.PosDef)
    (hm : 1 ≤ m) (i : Fin n) :
    |Real.log (grSq A i) - Real.log (grSq B i)| ≤ 2 * n * Real.log m := by
  have l0 := Real.log_nonneg hm
  rw [grSq_eq hA, grSq_eq hB, Real.log_div (lminor_re_pos hA _).1.ne' (lminor_re_pos hA _).1.ne',
    Real.log_div (lminor_re_pos hB _).1.ne' (lminor_re_pos hB _).1.ne']
  have a1 := h.abs_log_lminor hA hB hm i.succ
  have a2 := h.abs_log_lminor hA hB hm i.castSucc
  have e : |Real.log (lminor A i.succ).re - Real.log (lminor A i.castSucc).re -
      (Real.log (lminor B i.succ).re - Real.log (lminor B i.castSucc).re)| ≤
      |Real.log (lminor A i.succ).re - Real.log (lminor B i.succ).re| +
        |Real.log (lminor A i.castSucc).re - Real.log (lminor B i.castSucc).re| := by
    rw [show Real.log (lminor A i.succ).re - Real.log (lminor A i.castSucc).re -
        (Real.log (lminor B i.succ).re - Real.log (lminor B i.castSucc).re) =
        (Real.log (lminor A i.succ).re - Real.log (lminor B i.succ).re) -
          (Real.log (lminor A i.castSucc).re - Real.log (lminor B i.castSucc).re) by ring]
    exact abs_sub _ _
  have hi : ((i.succ : ℕ) : ℝ) + ((i.castSucc : ℕ) : ℝ) ≤ 2 * n := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    have := i.2
    have : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast this
    push_cast
    linarith
  calc _ ≤ _ := e
    _ ≤ ((i.succ : ℕ) : ℝ) * Real.log m + ((i.castSucc : ℕ) : ℝ) * Real.log m := add_le_add a1 a2
    _ = (((i.succ : ℕ) : ℝ) + ((i.castSucc : ℕ) : ℝ)) * Real.log m := by ring
    _ ≤ 2 * n * Real.log m := mul_le_mul_of_nonneg_right hi l0

end GlobalTheory.GradedCompare

namespace GlobalTheory.GradedCompare

open AlgebraicGeometry CategoryTheory Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Mean4O

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : FlagCpt Z e} {σ : F →+* ℂ}

theorem lnRatio_met (G G₀ : EigMet Z (embOf e σ)) (n : Letter Dw → ℤ) (p : Y.Y.pts σ) :
    ∃ g : Y.FrameAt p, lnRatio (C := cxSt F) (Y.met G n) (Y.met G₀ n) p =
      (Real.log (Y.genSq G n g) - Real.log (Y.genSq G₀ n g)) / 2 := by
  obtain ⟨q, h1, h2⟩ := Y.exists_adapted p
  refine ⟨q.2, ?_⟩
  have hm := FlagCpt.prodPow_mem n h1
  have key : ∀ (G' : EigMet Z (embOf e σ)) (f : Y.Y.FnC σ), Y.Y.pn σ _ (Y.met G' n) f p =
      ‖Var.fval (prodPow q.1 n) f p‖ ^ 2 * Y.genSq G' n q.2 := fun G' f => by
    rw [Var.pn_eq hm, FlagCpt.met_h G' n h2]
    simp [prodPow]
  have P1 : PosAt (C := cxSt F) (Y.met G n) p := posAt_of_posSet (FlagCpt.posSet_met G n) p
  unfold PosAt at P1
  unfold lnRatio lnN
  change Real.log (Y.Y.pn σ _ (Y.met G n) _ p) / 2 - Real.log (Y.Y.pn σ _ (Y.met G₀ n) _ p) / 2 = _
  change 0 < Y.Y.pn σ _ (Y.met G n) _ p at P1
  generalize ((cxSt F).cx Y.Y σ) (genAt (divOf Y n) (under p)) = f at P1 ⊢
  erw [key G f] at P1
  erw [key G f, key G₀ f]
  have g1 := FlagCpt.genSq_pos (Y := Y) G n q.2
  have g0 := FlagCpt.genSq_pos (Y := Y) G₀ n q.2
  have hA : ‖Var.fval (prodPow q.1 n) f p‖ ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at P1
    exact lt_irrefl _ P1
  rw [Real.log_mul hA g1.ne', Real.log_mul hA g0.ne']
  ring

theorem log_genSq (G : EigMet Z (embOf e σ)) (n : Letter Dw → ℤ) {p : Y.Y.pts σ} (g : Y.FrameAt p) :
    Real.log (Y.genSq G n g) = ∑ z : Letter Dw, (n z : ℝ) * Real.log (grSq (G.gram _ g z.1) z.2) := by
  unfold FlagCpt.genSq
  rw [Real.log_prod (fun z _ => zpow_ne_zero _ (grSq_pos (G.pos _ _ _) _).ne')]
  exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _

theorem abs_lnRatio_met_le (G G₀ : EigMet Z (embOf e σ)) (n : Letter Dw → ℤ) (p : Y.Y.pts σ) {m : ℝ} (hm : 1 ≤ m)
    (h : ∀ (g : Y.FrameAt p) (τ : E →+* ℂ), Cmp m (G.gram (Y.down p) g τ) (G₀.gram (Y.down p) g τ)) :
    |lnRatio (C := cxSt F) (Y.met G n) (Y.met G₀ n) p| ≤
      (∑ z : Letter Dw, |(n z : ℝ)| * (Dw.mult z.1 : ℝ)) * Real.log m := by
  obtain ⟨g, hg⟩ := lnRatio_met (Y := Y) G G₀ n p
  rw [hg, log_genSq, log_genSq, ← Finset.sum_sub_distrib, abs_div, abs_two, Finset.sum_mul]
  rw [div_le_iff₀ two_pos]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [← mul_sub, abs_mul]
  have b := (h g z.1).abs_log_grSq (G.pos _ _ _) (G₀.pos _ _ _) hm z.2
  calc |(n z : ℝ)| * |Real.log (grSq (G.gram _ g z.1) z.2) - Real.log (grSq (G₀.gram _ g z.1) z.2)|
      ≤ |(n z : ℝ)| * (2 * (Dw.mult z.1 : ℝ) * Real.log m) := mul_le_mul_of_nonneg_left b (abs_nonneg _)
    _ = |(n z : ℝ)| * (Dw.mult z.1 : ℝ) * Real.log m * 2 := by ring

end GlobalTheory.GradedCompare
