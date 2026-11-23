import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCBlk
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def LocSup (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (n b : ℕ) (a : List C.Letter) (h : C.LPt) : Prop :=
  ∃ B : ℝ, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + n - 1) a (h ++ [(n, t)]) (h ++ [(n, t)])‖ ≤ B

theorem psd_single_one {α : Type} (h : α) : TB.PSDOn ({h} : Finset α) (fun _ _ => (1 : ℂ)) := by
  unfold TB.PSDOn
  have hA : (Matrix.of fun (x y : ↥({h} : Finset α)) => (1 : ℂ)) =
      (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) *
        Matrix.conjTranspose (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) := by
    ext x y
    simp [Matrix.mul_apply]
  rw [hA]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem dlB_pos (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (b s : ℕ) : 0 < KB.dlB S b s := by
  have hd : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero E
    exact_mod_cast abs_pos.2 this
  have hrd : 0 < S6.rd E := Real.rpow_pos_of_pos hd _
  unfold KB.dlB D.deG
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  refine div_pos ?_ (div_pos two_pos (mul_pos hrd (pow_pos hg' 3)))
  first
  | exact pow_pos hrd _
  | exact zpow_pos hrd _
  | exact Real.rpow_pos_of_pos hrd _

theorem exists_word_of_admissible_at_place (S : C.HidaSetting E Wp Wq) {v : Fin S.f} {a : List C.Letter} (ha : D.AdmAt S v a) :
    ∃ w : S.W, w.1 v = a := ha

theorem locSup_one (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (a : List C.Letter) (ha : D.AdmAt S v a) (h : C.LPt)
    (hh : D.ptSize h = b - 1) : LocSup S v ε 1 b a h := by
  obtain ⟨w, hw⟩ := exists_word_of_admissible_at_place S ha
  obtain ⟨φ, -, hφ, ⟨Cφ, hCφ⟩, -⟩ := hI v ε hε b hb hbr w h h hh hh
  refine ⟨|Cφ| * ‖((S.sizeAt v a : ℝ) : ℂ)‖⁻¹, fun t ht => ?_⟩
  have hb1 : b + 1 - 1 = b := Nat.add_sub_cancel b 1
  unfold KB.gN
  rw [hb1, norm_div, div_eq_mul_inv, ← hw, ← hφ t ht]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
  have h1 : ((1 + ‖t‖) ^ 3)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg t]))
  have h2 : 0 ≤ ((1 + ‖t‖) ^ 3)⁻¹ := inv_nonneg.2 (by positivity)
  calc ‖φ t‖ ≤ Cφ * ((1 + ‖t‖) ^ 3)⁻¹ := hCφ t
    _ ≤ |Cφ| * ((1 + ‖t‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |Cφ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |Cφ| := mul_one _

theorem mL_one (K : ℕ) (L : ℝ) (σ : crystallineComparison.V 1) : crystallineComparison.mL K (fun _ => L) σ = crystallineComparison.mfac K L ‖σ 0‖ := by
  simp [crystallineComparison.mL]

theorem offdiag_bound {Z : Type} (w : Z → Z → ℂ) (a b : Z → Z → ℂ) (p : Z) (Y : Finset Z) (hp : p ∈ Y)
    (hB : KB.BlockPSD Y Y a w b) (Ba Bb : ℝ) (ha : (a p p).re ≤ Ba) (hb : (b p p).re ≤ Bb) :
    ‖w p p‖ ^ 2 ≤ Ba * Bb := by
  have hpsd := hB
  unfold KB.BlockPSD TB.PSDOn at hpsd
  let f : Fin 2 → ↥(Y.disjSum Y) := ![⟨Sum.inl p, by simp [hp]⟩, ⟨Sum.inr p, by simp [hp]⟩]
  have hs := hpsd.submatrix f
  have hdet := hs.det_nonneg
  have hd0 := hs.diag_nonneg (i := 0)
  have hd1 := hs.diag_nonneg (i := 1)
  rw [Matrix.det_fin_two] at hdet
  simp [f, Matrix.submatrix_apply] at hdet hd0 hd1
  rw [Complex.le_def] at hdet
  rw [Complex.nonneg_iff] at hd0 hd1
  have hw : ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := by
    have h3 := hdet.1
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, ← hd0.2, ← hd1.2] at h3
    nlinarith [h3]
  calc ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := hw
    _ ≤ Ba * Bb := mul_le_mul ha hb hd1.1 (le_trans hd0.1 ha)

end

end Formalism.FourierDecayAlt.P.PBC
