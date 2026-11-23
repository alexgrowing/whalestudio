import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTB

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem upper_utc {M : Matrix (Fin n) (Fin n) ℂ} (hM : M ∈ C2.UTset n) : G.upper (StabilizerDisintegration.utc M) = M := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dif_pos h, if_neg (ne_of_lt h), zero_add]
  · rw [dif_neg (lt_irrefl _), if_pos rfl, hM.2, add_zero]
  · rw [dif_neg (not_lt.2 h.le), if_neg (ne_of_gt h), hM.1 i j h, add_zero]

theorem upper_ut (v : G.UT n → ℂ) : G.upper v ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [G.upper, G.strictUpper, not_lt.2 h.le, ne_of_gt h]
  · simp [G.upper, G.strictUpper]

section gam

variable {r : ℕ} {X : Type}

def Gam (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) : (Fin r → Fin r → ℂ) × X :=
  (Matrix.of.symm (Matrix.of p.1.1 * Wm (Matrix.of p.1.1) * G.upper p.2), p.1.2)

theorem Gam_det (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) :
    (Matrix.of (Gam p).1).det = (Matrix.of p.1.1).det := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Matrix.det_mul, Matrix.det_mul, C2x2.ut_det (Wm_ut _), C2x2.ut_det (upper_ut p.2), mul_one, mul_one]

theorem Gam_eq (q : (Fin r → Fin r → ℂ) × X) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (Matrix.of q.1).det ≠ 0)
    (hu : u ∈ C2.UTset r) : Gam ((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))) = q := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Wm_mul hdet hu, upper_utc (Sm_ut _), Matrix.mul_assoc (Matrix.of q.1) u,
    Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc, Wm_mul_Sm, Matrix.mul_one]
  rfl

theorem Gam_cont [TopologicalSpace X] (S : Set (((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)))
    (hS : ∀ p ∈ S, (Matrix.of p.1.1).det ≠ 0) : ContinuousOn Gam S := by
  have hW : ∀ a b : Fin r, ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) => Wm (Matrix.of p.1.1) a b) S :=
    fun a b => (cd_Wm a b).continuousOn.comp (continuous_fst.comp continuous_fst).continuousOn fun p hp => hS p hp
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_)
    (continuous_snd.comp continuous_fst).continuousOn
  have e : ∀ p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ),
      (Gam p).1 a b = ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b := by
    intro p
    simp only [Gam]
    rfl
  have key : ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) =>
      ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b) S := by
    refine continuousOn_finsetSum _ fun c _ => ContinuousOn.mul (continuousOn_finsetSum _ fun d _ => ?_) ?_
    · exact (((continuous_apply_apply a d).comp (continuous_fst.comp continuous_fst)).continuousOn).mul (hW d c)
    · exact ((continuous_apply_apply c b).comp (Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper.comp continuous_snd)).continuousOn
  exact key.congr fun p _ => e p

end gam

theorem top_truncation_construction : MkTopCut := by
  intro r
  let φ : ContDiffBump (0 : G.UT r → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set β₀ : (G.UT r → ℂ) → ℝ := φ.normed volume with hβ₀
  have hcont : Continuous β₀ := φ.continuous_normed
  refine ⟨fun Z => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z))), ?_, ?_, ?_⟩
  · have hS : ContDiffOn ℝ ∞ (fun Z : Fin r → Fin r → ℂ => StabilizerDisintegration.utc (Sm (Matrix.of Z)))
        {Z | (Matrix.of Z).det ≠ 0} :=
      contDiffOn_pi.2 fun q => cd_Sm q.1.1 q.1.2
    exact (φ.contDiff_normed (n := ⊤)).comp_contDiffOn hS
  · intro Z hZ
    have hmp := Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (Sm_ut (Matrix.of Z))
    have hfun : (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) =
        fun v => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z) * G.upper v)) := by
      funext v
      simp only [Equiv.apply_symm_apply]
      rw [Sm_mul hZ (upper_ut v)]
    show Integrable (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) ∧
      ∫ v : G.UT r → ℂ, β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v))))) = 1
    rw [hfun]
    constructor
    · have hi := (integrable_map_measure hcont.aestronglyMeasurable hmp.measurable.aemeasurable).1
        (by rw [hmp.map_eq]; exact φ.integrable_normed)
      exact hi
    · rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]
      exact φ.integral_normed
  · intro X _ K hK hKdet
    have hC₀ : IsCompact (tsupport β₀) := φ.hasCompactSupport_normed
    refine ⟨Gam '' (K ×ˢ tsupport β₀), (hK.prod hC₀).image_of_continuousOn (Gam_cont _ fun p hp => hKdet _ hp.1), ?_, ?_⟩
    · rintro q ⟨⟨q', c⟩, ⟨hq', -⟩, rfl⟩
      exact ⟨by rw [Gam_det]; exact hKdet q' hq', q', hq', rfl⟩
    · rintro q hdet hβ ⟨u, hu, hK'⟩
      have huT : u ∈ C2.UTset r := ⟨fun i j h => hu.1 h, hu.2⟩
      exact ⟨((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))),
        ⟨hK', subset_tsupport _ hβ⟩, Gam_eq q u hdet huT⟩

end Formalism.FourierDecayAlt.P.CutEXMT
