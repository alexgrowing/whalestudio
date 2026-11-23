import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepBlock

variable {N : ℕ}

abbrev sq (T : Matrix (Fin N) (Fin N) ℂ) (P : Fin N → Prop) : Matrix {a // P a} {a // P a} ℂ :=
  T.submatrix Subtype.val Subtype.val

def sd (T : Matrix (Fin N) (Fin N) ℂ) (P : Fin N → Prop) [DecidablePred P] : ℂ := (sq T P).det

theorem sd_congr (T : Matrix (Fin N) (Fin N) ℂ) {P Q : Fin N → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P a ↔ Q a) : sd T P = sd T Q := by
  unfold sd
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight h) (sq T Q)]
  rfl

theorem sd_split (T : Matrix (Fin N) (Fin N) ℂ) (P Q : Fin N → Prop) [DecidablePred P] [DecidablePred Q]
    (hz : ∀ a b, P a → P b → ¬ Q a → Q b → T a b = 0) :
    sd T P = sd T (fun a => P a ∧ Q a) * sd T (fun a => P a ∧ ¬ Q a) := by
  have key := Matrix.twoBlockTriangular_det (sq T P) (fun x => Q x.1) (fun x hx y hy => hz _ _ x.2 y.2 hx hy)
  unfold sd
  rw [key]
  congr 1
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeSubtypeEquivSubtypeInter P Q).symm]
    rfl
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeSubtypeEquivSubtypeInter P (fun a => ¬ Q a)).symm]
    rfl

theorem det_eq_sd_mul (T : Matrix (Fin N) (Fin N) ℂ) (Q : Fin N → Prop) [DecidablePred Q]
    (hz : ∀ a, ¬ Q a → ∀ b, Q b → T a b = 0) : T.det = sd T Q * sd T (fun a => ¬ Q a) :=
  Matrix.twoBlockTriangular_det T Q hz

theorem minor_eq_sd (T : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    minorIJ T S S = sd T (· ∈ S) := by
  unfold minorIJ sd
  rw [dif_pos rfl]
  let e : Fin S.card ≃ {a // a ∈ S} := (S.orderIsoOfFin rfl).toEquiv
  letI : Fintype {a // a ∈ S} := Subtype.fintype (· ∈ S)
  refine Eq.trans ?_ (Matrix.det_submatrix_equiv_self e (sq T (· ∈ S)))
  congr 1

theorem sd_pos {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.PosDef) (P : Fin N → Prop) [DecidablePred P] :
    0 < sd T P :=
  (hT.submatrix Subtype.val_injective).det_pos

theorem sub_mul_of (A B : Matrix (Fin N) (Fin N) ℂ) (Q : Fin N → Prop) [DecidablePred Q]
    (hz : ∀ a b c, Q a → ¬ Q b → Q c → A a b * B b c = 0) :
    sq (A * B) Q = sq A Q * sq B Q := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q, Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ Q x})),
    add_zero]
  intro b _
  exact hz _ _ _ a.2 b.2 c.2

theorem sub_conj (h X : Matrix (Fin N) (Fin N) ℂ) (Q : Fin N → Prop) [DecidablePred Q]
    (hh : ∀ a b, ¬ Q a → Q b → h a b = 0) :
    sq (hᴴ * X * h) Q = (sq h Q)ᴴ * sq X Q * sq h Q := by
  rw [sub_mul_of _ _ Q (fun a b c _ hb hc => by rw [hh b c hb hc, mul_zero]),
    sub_mul_of _ _ Q (fun a b c ha hb _ => by rw [Matrix.conjTranspose_apply, hh b a hb ha, star_zero, zero_mul]),
    Matrix.conjTranspose_submatrix]

theorem pos_norm {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hz
  have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him.symm])
  rw [this, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, abs_of_pos hre]

theorem mul_re_of_pos {x y : ℂ} (hx : 0 < x) (hy : 0 < y) : (x * y).re = x.re * y.re := by
  rw [Complex.mul_re, ← (Complex.pos_iff.mp hx).2]
  simp

theorem sd_conj_re (h G : Matrix (Fin N) (Fin N) ℂ) (Q : Fin N → Prop) [DecidablePred Q]
    (hh : ∀ a b, ¬ Q a → Q b → h a b = 0) :
    (sd (hᴴ * G * h) Q).re = ‖sd h Q‖ ^ 2 * (sd G Q).re := by
  have e : sd (hᴴ * G * h) Q = ((‖sd h Q‖ ^ 2 : ℝ) : ℂ) * sd G Q := by
    unfold sd
    rw [sub_conj h G Q hh, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have := Complex.conj_mul' (sq h Q).det
    push_cast
    rw [← this]
    simp only [Complex.star_def]
    ring
  rw [e, Complex.re_ofReal_mul]

theorem blockDiag_conj {j : ℕ} {h G : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hG : IsBlockDiag j G) :
    IsBlockDiag j (hᴴ * G * h) := by
  have mul : ∀ {A B : Matrix (Fin N) (Fin N) ℂ}, IsBlockDiag j A → IsBlockDiag j B → IsBlockDiag j (A * B) := by
    intro A B hA hB a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (a : ℕ) < N - j ↔ (c : ℕ) < N - j
    · rw [hB c b (fun hcb => hab (hc.trans hcb)), mul_zero]
    · rw [hA a c hc, zero_mul]
  refine mul (mul (fun a b hab => ?_) hG) hh
  rw [Matrix.conjTranspose_apply, hh b a (fun e => hab e.symm), star_zero]

theorem posDef_conj {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hd : h.det ≠ 0) : (hᴴ * G * h).PosDef :=
  hG.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)))

end GlobalTheory.CompanionTheory.Ar.PB.StepBlock

namespace GlobalTheory.CompanionTheory.Ar.PB.StepBlock
variable {N : ℕ}

abbrev Lt (k : ℕ) : Fin N → Prop := fun a => (a : ℕ) < k

abbrev Ge (k : ℕ) : Fin N → Prop := fun a => k ≤ (a : ℕ)

abbrev Seg (k l : ℕ) : Fin N → Prop := fun a => k ≤ (a : ℕ) ∧ (a : ℕ) < l

theorem sd_lead {j : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} (hT : IsBlockDiag j T) (m : ℕ) :
    sd T (Lt (N - j + m)) = sd T (Lt (N - j)) * sd T (Seg (N - j) (N - j + m)) := by
  rw [sd_split T (Lt (N - j + m)) (Lt (N - j)) (fun a b _ _ ha hb => hT a b fun e => ha (e.2 hb))]
  congr 1
  · exact sd_congr T fun a => by simp only [Lt]; omega
  · exact sd_congr T fun a => by simp only [Lt, Seg]; omega

theorem minor_stepCols_le {j : ℕ} (i : Fin N) (c : (i : ℕ) + 1 ≤ j) (T : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ T (stepCols N j i) (stepCols N j i) = sd T (Seg (N - j) (N - j + ((i : ℕ) + 1))) := by
  rw [minor_eq_sd]
  exact sd_congr T fun a => by simp [stepCols, c]

theorem minor_stepCols_gt {j : ℕ} (i : Fin N) (c : ¬ (i : ℕ) + 1 ≤ j) (T : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ T (stepCols N j i) (stepCols N j i) = sd T (Lt ((i : ℕ) + 1 - j)) := by
  rw [minor_eq_sd]
  exact sd_congr T fun a => by simp [stepCols, c]

theorem minor_wIdx (j : ℕ) (T : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ T (wIdx N j) (wIdx N j) = sd T (Ge (N - j)) := by
  rw [minor_eq_sd]
  exact sd_congr T fun a => by simp [wIdx]

theorem minor_omIdx (j : ℕ) (T : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ T (omIdx N j) (omIdx N j) = sd T (Lt (N - j)) := by
  rw [minor_eq_sd]
  exact sd_congr T fun a => by simp [omIdx]

theorem sd_lt_zero (T : Matrix (Fin N) (Fin N) ℂ) : sd T (Lt 0) = 1 := by
  haveI : IsEmpty {a : Fin N // Lt 0 a} := ⟨fun a => Nat.not_lt_zero _ a.2⟩
  exact Matrix.det_isEmpty

theorem inFlagDomain_mul {j : ℕ} {Pi h : Matrix (Fin N) (Fin N) ℂ} (hP : InFlagDomain N j Pi)
    (hh : IsBlockDiag j h) (hd : h.det ≠ 0) : InFlagDomain N j (Pi * h) := by
  refine ⟨by rw [Matrix.det_mul]; exact hP.1.mul (isUnit_iff_ne_zero.2 hd), ?_⟩
  have hz : ∀ a b, ¬ Lt (N := N) (N - j) a → Lt (N := N) (N - j) b → h a b = 0 :=
    fun a b ha hb => hh a b fun e => ha (e.2 hb)
  have hz' : ∀ a, ¬ Lt (N := N) (N - j) a → ∀ b, Lt (N := N) (N - j) b → h a b = 0 :=
    fun a ha b hb => hz a b ha hb
  have hdet : (sq h (Lt (N - j))).det ≠ 0 := by
    intro e
    apply hd
    rw [det_eq_sd_mul h (Lt (N - j)) hz']
    show (sq h (Lt (N - j))).det * _ = 0
    rw [e, zero_mul]
  have hgram : gramOf (sigForm N j) (Pi * h) = hᴴ * gramOf (sigForm N j) Pi * h := by
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e1 : gramHead (sigForm N j) (N - j) (Pi * h) =
      (sq h (Lt (N - j)))ᴴ * gramHead (sigForm N j) (N - j) Pi * sq h (Lt (N - j)) := by
    unfold gramHead
    rw [hgram]
    exact sub_conj h _ (Lt (N - j)) hz
  rw [e1]
  have e2 : -((sq h (Lt (N - j)))ᴴ * gramHead (sigForm N j) (N - j) Pi * sq h (Lt (N - j))) =
      (sq h (Lt (N - j)))ᴴ * (-gramHead (sigForm N j) (N - j) Pi) * sq h (Lt (N - j)) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  rw [e2]
  exact hP.2.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)))

theorem gramLog_eq {j : ℕ} {Pi G h : Matrix (Fin N) (Fin N) ℂ} (hP : IsPeriodGram j Pi G)
    (hh : IsBlockDiag j h) (hH : (hᴴ * G * h).PosDef) (k : ℕ) :
    gramLog (sigForm N j) k (Pi * h) = (1 / 2) * Real.log (sd (hᴴ * G * h) (Lt k)).re := by
  unfold gramLog
  rw [hP.2 h hh k, ← pos_norm (sd_pos hH (Lt k))]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.StepBlock

namespace GlobalTheory.CompanionTheory.Ar.PB

open StepBlock in

theorem stepPot_mul_eq_blockPot : ∀ (N j : ℕ) (i : Fin N) (Pi G h : Matrix (Fin N) (Fin N) ℂ), j ≤ N →
    IsPeriodGram j Pi G → IsBlockDiag j G → G.PosDef → IsBlockDiag j h → h.det ≠ 0 →
    InFlagDomain N j (Pi * h) ∧ stepPot N j i (Pi * h) = blockPot j i G h + Real.log ‖detFac j i h‖ := by
  intro N j i Pi G h hj hP hG hGp hh hd
  refine ⟨inFlagDomain_mul hP.1 hh hd, ?_⟩
  have hH := posDef_conj (h := h) hGp hd
  have hHb := blockDiag_conj hh hG
  have hg := gramLog_eq hP hh hH
  have zO : ∀ a b, ¬ Lt (N := N) (N - j) a → Lt (N := N) (N - j) b → h a b = 0 :=
    fun a b ha hb => hh a b fun e => ha (e.2 hb)
  have zW : ∀ a b, ¬ Ge (N := N) (N - j) a → Ge (N := N) (N - j) b → h a b = 0 :=
    fun a b ha hb => hh a b fun e => absurd hb (not_le.2 (e.1 (not_le.1 ha)))
  have hsplit : h.det = sd h (Lt (N - j)) * sd h (Ge (N - j)) := by
    rw [det_eq_sd_mul h (Lt (N - j)) (fun a ha b hb => zO a b ha hb)]
    congr 1
    exact sd_congr h fun a => by simp only [Lt, Ge]; omega
  have ndO : 0 < ‖sd h (Lt (N - j))‖ := norm_pos_iff.2 fun e => hd (by rw [hsplit, e, zero_mul])
  have ndW : 0 < ‖sd h (Ge (N - j))‖ := norm_pos_iff.2 fun e => hd (by rw [hsplit, e, mul_zero])
  have halfLog : ∀ d a : ℝ, 0 < d → 0 < a → (1 / 2) * Real.log (d ^ 2 * a) = (1 / 2) * Real.log a + Real.log d := by
    intro d a hd ha
    rw [Real.log_mul (by positivity) ha.ne', Real.log_pow]
    push_cast
    ring
  have rePos : ∀ {x : ℂ}, 0 < x → 0 < x.re := fun hx => (Complex.pos_iff.mp hx).1
  have logMul : ∀ x y : ℂ, 0 < x → 0 < y →
      (1 / 2) * Real.log (x * y).re = (1 / 2) * Real.log x.re + (1 / 2) * Real.log y.re := by
    intro x y hx hy
    rw [mul_re_of_pos hx hy, Real.log_mul (rePos hx).ne' (rePos hy).ne']
    ring
  have logW : (1 / 2) * Real.log (sd (hᴴ * G * h) (Ge (N - j))).re =
      (1 / 2) * Real.log (sd G (Ge (N - j))).re + Real.log ‖sd h (Ge (N - j))‖ := by
    rw [sd_conj_re h G _ zW]
    exact halfLog _ _ ndW (rePos (sd_pos hGp _))
  have logO : (1 / 2) * Real.log (sd (hᴴ * G * h) (Lt (N - j))).re =
      (1 / 2) * Real.log (sd G (Lt (N - j))).re + Real.log ‖sd h (Lt (N - j))‖ := by
    rw [sd_conj_re h G _ zO]
    exact halfLog _ _ ndO (rePos (sd_pos hGp _))
  have hN : sd (hᴴ * G * h) (Lt N) = sd (hᴴ * G * h) (Lt (N - j)) * sd (hᴴ * G * h) (Ge (N - j)) := by
    have key := sd_lead hHb j
    rw [Nat.sub_add_cancel hj] at key
    rw [key]
    congr 1
    exact sd_congr _ fun a => by have := a.2; simp only [Seg, Ge]; omega
  by_cases c1 : (i : ℕ) + 1 ≤ j
  · have stepA : stepPot N j i (Pi * h) =
        (1 / 2) * Real.log (sd (hᴴ * G * h) (Seg (N - j) (N - j + ((i : ℕ) + 1)))).re := by
      rw [stepPot, if_pos c1, hg, hg, sd_lead hHb, logMul _ _ (sd_pos hH _) (sd_pos hH _)]
      ring
    by_cases c2 : (i : ℕ) + 1 = j
    · have hS : sd (hᴴ * G * h) (Seg (N - j) (N - j + ((i : ℕ) + 1))) = sd (hᴴ * G * h) (Ge (N - j)) :=
        sd_congr _ fun a => by have := a.2; simp only [Seg, Ge]; omega
      have np : ¬ IsProperStep N j i := fun q => q.1 c2
      rw [stepA, hS, logW, blockPot, if_neg np, add_zero]
      by_cases c3 : (i : ℕ) + 1 = N
      · have om : ∀ T : Matrix (Fin N) (Fin N) ℂ, sd T (Lt (N - j)) = 1 := fun T => by
          rw [← sd_lt_zero T]
          exact sd_congr T fun a => by simp only [Lt]; omega
        have hdf : ∀ T : Matrix (Fin N) (Fin N) ℂ, detFac j i T = sd T (Ge (N - j)) := fun T => by
          rw [detFac, if_pos c2.ge, if_pos c3, minor_wIdx, minor_omIdx, om, mul_one]
        rw [hdf, hdf]
      · have hdf : ∀ T : Matrix (Fin N) (Fin N) ℂ, detFac j i T = sd T (Ge (N - j)) := fun T => by
          rw [detFac, if_pos c2.ge, if_neg c3, minor_wIdx, mul_one]
        rw [hdf, hdf]
    · have pr : IsProperStep N j i := ⟨c2, by omega⟩
      have hdf : ∀ T : Matrix (Fin N) (Fin N) ℂ, detFac j i T = 1 := fun T => by
        rw [detFac, if_neg (by omega), if_neg (by omega), mul_one]
      rw [stepA, blockPot, if_pos pr, hdf, hdf, minor_stepCols_le i c1]
      simp
  · have stepB : stepPot N j i (Pi * h) = (1 / 2) * Real.log (sd (hᴴ * G * h) (Ge (N - j))).re +
        (1 / 2) * Real.log (sd (hᴴ * G * h) (Lt ((i : ℕ) + 1 - j))).re := by
      rw [stepPot, if_neg c1, hg, hg, hg, hN, logMul _ _ (sd_pos hH _) (sd_pos hH _)]
      ring
    by_cases c3 : (i : ℕ) + 1 = N
    · have np : ¬ IsProperStep N j i := fun q => q.2 c3
      have hL : sd (hᴴ * G * h) (Lt ((i : ℕ) + 1 - j)) = sd (hᴴ * G * h) (Lt (N - j)) :=
        sd_congr _ fun a => by simp only [Lt]; omega
      have hdf : ∀ T : Matrix (Fin N) (Fin N) ℂ, detFac j i T = sd T (Ge (N - j)) * sd T (Lt (N - j)) := fun T => by
        rw [detFac, if_pos (by omega), if_pos c3, minor_wIdx, minor_omIdx]
      rw [stepB, hL, logW, logO, blockPot, if_neg np, add_zero, hdf, hdf,
        logMul _ _ (sd_pos hGp _) (sd_pos hGp _), norm_mul, Real.log_mul ndW.ne' ndO.ne']
      ring
    · have pr : IsProperStep N j i := ⟨by omega, c3⟩
      have hdf : ∀ T : Matrix (Fin N) (Fin N) ℂ, detFac j i T = sd T (Ge (N - j)) := fun T => by
        rw [detFac, if_pos (by omega), if_neg c3, minor_wIdx, mul_one]
      rw [stepB, logW, blockPot, if_pos pr, hdf, hdf, minor_stepCols_gt i c1]
      ring

end GlobalTheory.CompanionTheory.Ar.PB
