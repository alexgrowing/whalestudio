import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem cutF_approximants_ccle :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs χ f A₀ ε A mm hχ hε _ hfA hA
  obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hχ hfA hε (A + 1) mm hA
  generalize D.cutF Bs χ f ε = H at hb ⊢
  have hb0 : 0 ≤ b := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hb
  have hb' : B.CCle A mm H b := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := k) (r := r) (E := Wq →L[ℂ] Wp) mm
  have hψ : ∀ n : ℕ, B.CCle A mm (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g)
      (Kp * b / ((n : ℝ) + 1)) := fun n => by
    have h := hKp ((n : ℝ) + 1) (by positivity) (A + 1) H b hb
    rwa [add_sub_cancel_right] at h
  have hc : ∀ (n : ℕ) (g : B.Mat k r), ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)
        = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := fun n g =>
    Formalism.FourierDecayAlt.P.PBE.cut_eq (fun (n : ℕ) (g : B.Mat k r) => ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (fun _ _ => rfl) n g
  have hKb : 0 ≤ Kp * b := mul_nonneg hKp0 hb0
  refine ⟨b + Kp * b, by positivity, Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (by linarith), fun n => ⟨?_, ?_⟩⟩
  · have e : (fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g)
          = fun g => H g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [hc n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * b / ((n : ℝ) + 1) ≤ Kp * b := div_le_self hKb (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  · have e : ((fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) - H)
          = fun g => (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [Pi.sub_apply, hc n g, sub_smul, one_smul, neg_one_smul, sub_sub_cancel_left]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n)) ?_
    simp only [norm_neg, norm_one, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end GlobalTheory
