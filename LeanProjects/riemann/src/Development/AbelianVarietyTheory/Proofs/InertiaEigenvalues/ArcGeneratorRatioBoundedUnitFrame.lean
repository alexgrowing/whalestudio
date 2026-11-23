import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

open scoped Matrix

namespace GlobalTheory.ArcGenBound

open Matrix

theorem affine_pos {T a b c : ℝ} (h : ∀ x s : ℝ, T < s → 0 < a + x * b + s * c) : b = 0 ∧ 0 ≤ c := by
  have h1 := h 0 (T + 1) (by linarith)
  constructor
  · by_contra hb
    have := h (-(a + (T + 1) * c) / b) (T + 1) (by linarith)
    rw [div_mul_cancel₀ _ hb] at this
    linarith
  · by_contra hc
    have hc' : 0 < -c := by linarith [not_le.1 hc]
    have hd : 0 < (a + (T + 1) * c) / (-c) := div_pos (by linarith) hc'
    have := h 0 (T + 1 + (a + (T + 1) * c) / (-c)) (by linarith)
    have e := div_mul_cancel₀ (a + (T + 1) * c) hc'.ne'
    nlinarith

theorem det_im_lower_bound {g : ℕ} (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (T : ℝ) (A B : Matrix (Fin g) (Fin g) ℂ)
    (haff : ∀ w, τ w = A + w • B) (hpos : ∀ w : ℂ, T < w.im → ((τ w).map Complex.im).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, T + 1 < w.im → C ≤ ((τ w).map Complex.im).det := by
  have hq : ∀ (w : ℂ) (v : Fin g → ℝ), v ⬝ᵥ ((τ w).map Complex.im) *ᵥ v = v ⬝ᵥ (A.map Complex.im) *ᵥ v +
      w.re * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + w.im * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := by
    intro w v
    have e : (τ w).map Complex.im = A.map Complex.im + w.re • B.map Complex.im + w.im • B.map Complex.re := by
      ext i j
      simp [haff, add_assoc]
    rw [e]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h0 : T < (⟨0, T + 1⟩ : ℂ).im := by simp
  refine ⟨((τ ⟨0, T + 1⟩).map Complex.im).det, (hpos _ h0).det_pos, fun w hw => ?_⟩
  have hw' : T < w.im := by linarith
  have hD : ((τ w).map Complex.im - (τ ⟨0, T + 1⟩).map Complex.im).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hpos w hw').isHermitian.sub (hpos _ h0).isHermitian) fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hp : ∀ x s : ℝ, T < s → 0 < v ⬝ᵥ (A.map Complex.im) *ᵥ v +
        x * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + s * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := fun x s hs => by
      have := (hpos ⟨x, s⟩ hs).dotProduct_mulVec_pos hv
      rwa [star_trivial, hq] at this
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hq, hq]
    obtain ⟨hb, hc⟩ := affine_pos hp
    have := mul_nonneg (sub_pos.2 hw).le hc
    rw [hb]
    dsimp only
    linarith
  have := GlobalTheory.ClassFin.gramLB_det_mono (hpos _ h0) hD
  rwa [add_sub_cancel] at this

end GlobalTheory.ArcGenBound

open GlobalTheory.ArcGenBound in

theorem GlobalTheory.ArcGenBound.gen_ratio_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z _ _ _
  have haff : ∀ w, Θ.τ w = Matrix.of (fun i k => (Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) i) +
      w • Matrix.of (fun i k => (Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) i) := by
    intro w
    ext i k
    have e := congrFun (Θ.per w k).2 i
    rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e
    simpa [Matrix.transpose_apply] using e.symm
  obtain ⟨C, hC, hdet⟩ := det_im_lower_bound Θ.τ Ha.T _ _ haff (fun w hw => (Θ.pos w hw).2)
  refine ⟨Ha.T + 1, Real.sqrt (‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ Uw.g * C))⁻¹), ?_⟩
  intro w hw yw hA k x t hx hb
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨hLie, hGen⟩ := hA
  have V1 := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W Uw.g _ Uw.F Ha th Θ w yw hw' hLie.1 hGen
  have V2 := Uw.norm k x hx
  obtain ⟨G, -, -, hchg⟩ := (GlobalTheory.Frames.frBor_iff_frChg _ _ _).1 hb
  have hs := (GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 E H Dw l Xo c
    σ Uw.g _ Uw.F (Uw.ik k) Ha.i (Uw.Pm k x) (Ha.Pw w) (U.un k x) yw G (t none : CAt σ) 1 _ (Uw.period k x)
    (Ha.period w hw') (Uw.lie k x).1 hLie.1 hchg V2 V1).2
  rw [mul_one] at hs
  apply Real.le_sqrt_of_sq_le
  rw [← hs]
  have hd := hdet w hw
  have h2 : (0 : ℝ) < 2 ^ Uw.g := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (Real.sqrt_pos.2 (mul_pos h2 hC)) (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd h2.le))
