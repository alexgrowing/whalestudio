import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGraded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section thr

theorem thr_of_budget {k r m N : ℕ} {A₀ : ℝ}
    (hm : 6 * ((r : ℝ) + 1) * m + 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A₀)
    (hA : 10 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    JF.TransportedAlt k r A₀ m := by
  unfold JF.TransportedAlt
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn] at hm ⊢
  rw [lt_div_iff₀ (by positivity)]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, mul_zero, sub_zero] at hm ⊢
    have hn1 : (1 : ℝ) ≤ 2 * (r : ℝ) + k + 1 := by linarith
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
    have hP : 1 ≤ ((r : ℝ) + 1) ^ 3 * (2 * (r : ℝ) + k + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr1) hn1
    have h3 : ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * (2 * (r : ℝ) + k + 1) ^ 3 := by
      calc ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 = ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 * 1 := by ring
        _ ≤ ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 * (((r : ℝ) + 1) ^ 3 * (2 * (r : ℝ) + k + 1)) :=
            mul_le_mul_of_nonneg_left hP (by positivity)
        _ = ((r : ℝ) + 1) ^ 4 * (2 * (r : ℝ) + k + 1) ^ 3 := by ring
    have hN : 0 ≤ ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2) := by positivity
    have hpos2 : 0 < ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
    nlinarith [h3, hN, hpos2, hA]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    nlinarith [hm, hm1]

end thr

section jf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jf_mem_FFlM [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hT : JF.TransportedAlt k r A m) (hF : B.InCC A m F) :
    B.JF D F ∈ FFlM (m : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
    D.haarN.conc (fun n₀ h => D.haarN.left n₀ h)
  have hW := Formalism.FourierDecayAlt.P.bessel_words_of_domain Formalism.FourierDecayAlt.P.bessel_integral_domain
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, he⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
      D.haarN.conc D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
      (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

end jf

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
