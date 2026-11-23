import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSignsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSkewHermitianBasisVectorEqSqrtTwoStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem riemLie_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  classical
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI t ht
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  set z : Fin r := ⟨0, hr⟩ with hz
  set d := sgnR σ e with hd_def
  have hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1 := fun τ a => by
    simp only [d, sgnR]; split_ifs <;> simp
  have hinv := det_ne_zero_of_isIdent hI
  have hvW : ∀ k, boxVec d z k ∈ W := fun k =>
    (GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs E r κ p q Ψ G x σ A e hI _).2 (GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond E r Ψ d z hd k)
  let K := Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}
  let w : K → W := fun k => ⟨boxVec d z k, hvW k⟩
  have hdual := GlobalTheory.T.skewHermitianCoordinate_dual_basisVector E r Ψ d z hd
  have hcoord : ∀ (g : K → ℝ) j, boxCoord z j ((∑ k, g k • w k : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = g j := by
    intro g j
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, w, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_eq_single j (fun k hk => by rw [if_neg (Ne.symm hk)])]
    rw [if_pos rfl]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := hcoord g j
    rw [hg] at this
    simpa using this.symm
  have hcardK : Fintype.card K = Ψ.card * (r ^ 2 - 1) := by
    simp [K, Fintype.card_prod, Fintype.card_coe, sq]
  have hfin : Fintype.card K = Module.finrank ℝ W := by
    refine le_antisymm hli.fintype_card_le_finrank ?_
    rw [hcardK]
    rcases Ψ.eq_empty_or_nonempty with h0 | ⟨τ0, hτ0⟩
    · have hs : Subsingleton W := ⟨fun a b => Subtype.ext (PiLp.ext fun m => by
        have := m.1.2; simp [h0] at this)⟩
      rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _
    · have hG : G.det ≠ 0 := by
        intro h
        apply (hinv ⟨τ0, hτ0⟩).2
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      exact finrank_comap_realLie_le Ψ G x hr hG fun τ => (hinv τ).1
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hfin
  have hrep : ∀ Y : W, Y = ∑ k, boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) • w k := by
    intro Y
    have hYs : Y ∈ Submodule.span ℝ (Set.range w) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hYs
    have h2 : ∀ j, boxCoord z j (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = c j := by
      intro j
      rw [← hc]
      exact hcoord _ j
    simp_rw [h2]; exact hc.symm
  set S := {X : Ψ → Fin r → Fin r → ℂ | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} with hS_def
  have hSo : IsOpen S := by
    simp only [hS_def, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    have : Continuous fun X : Ψ → Fin r → Fin r → ℂ => Matrix.of (X τ) := continuous_apply τ
    exact (((continuous_const.matrix_mul this).matrix_mul continuous_const).matrix_elem a b).norm
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  unfold riemLie
  rw [Measure.map_apply hf hSo.measurableSet, OrthonormalBasis.addHaar_eq_volume]
  have key1 : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * M * (mat x τ)⁻¹) * mat x τ = M := fun τ M => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hinv τ).1.isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hinv τ).1.isUnit]
  have hsub : (fun Y : W => fromFrame x Y.1) ⁻¹' S ⊆
      {y : W | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} := by
    intro Y hY
    have hY' : ∀ τ a b, ‖(Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)‖ < t := by
      intro τ a b
      have := hY τ a b
      have e1 : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rwa [e1, key1] at this
    refine ⟨fun k => boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)), fun k => ?_, hrep Y⟩
    obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
    simp only [boxCoord]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
  refine (measure_mono hsub).trans ((GlobalTheory.T.volume_coordinateBox_le_hadamard W K w t ht.le hfin).trans (ENNReal.ofReal_le_ofReal ?_))
  have hn : ∀ k, ‖w k‖ = √2 := fun k => GlobalTheory.T.norm_skewHermitianBasisVector_eq_sqrt_two E r Ψ d z hd k
  simp only [hn, Finset.prod_const, Finset.card_univ]
  rw [hcardK, ← mul_pow]
  have h2 : 2 * t * √2 ≤ 3 * t := by
    have hs : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  exact pow_le_pow_left₀ (by positivity) h2 _

end GlobalTheory.CovTop.VolUp.FrameBox
