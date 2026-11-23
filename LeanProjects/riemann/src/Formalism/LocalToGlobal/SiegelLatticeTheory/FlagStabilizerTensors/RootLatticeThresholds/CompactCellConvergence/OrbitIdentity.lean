import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.PairMeasBad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem rmulF_meas (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) ρ) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Formalism.FourierDecayAlt.B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  first
  | exact (measurable_pi_iff.mp (measurable_pi_apply i) l).mul measurable_const
  | fun_prop

theorem orbit_identity (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} (hR : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μR)
    (hRc : μR {x | Matrix.of x ∉ RStab k r γ} = 0) (hR0 : μR ≠ 0)
    {ν : Measure (PairSp k r)} (hQ : IsOrbQuot L γ μR ν)
    (F : PairSp k r → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ x, Good L x → ∀ a ∈ RStab k r γ, F (stabAct γ a x) = F x)
    (E : Set (Mt k r)) (hE : MeasurableSet E) (A : Set (Mt k r)) (hA : MeasurableSet A)
    (ρh : Mt k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hρ : ∀ n : Mt k r, Matrix.of n ∈ Nset k r → ρh n ∈ RStab k r γ ∧
      ∀ a : Mt k r, Matrix.of a ∈ RStab k r γ →
        ((fun i j => (Matrix.of a * Matrix.of n) i j : Mt k r) ∈ E ↔ Formalism.FourierDecayAlt.B.rmulF (ρh n) a ∈ A)) :
    ∫⁻ x, F x * E.indicator (1 : Mt k r → ℝ≥0∞) x.1.2 ∂(pairMeas L) = μR A * ∫⁻ x, F x ∂ν := by
  have hfst : Measurable (fun x : PairSp k r => x.1.2) := measurable_snd.comp measurable_fst
  have hf : Measurable (fun x : PairSp k r => F x * E.indicator (1 : Mt k r → ℝ≥0∞) x.1.2) :=
    hF.mul ((measurable_one.indicator hE).comp hfst)
  rw [hQ _ hf, ← lintegral_const_mul _ hF]
  have hgood : ∀ᵐ x ∂ν, Good L x := by
    rw [ae_iff]
    exact nu_bad L hR0 hRc hQ
  have hstab : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := by
    rw [ae_iff]
    simpa using hRc
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with x hx
  obtain ⟨hρn, hiff⟩ := hρ x.1.2 hx.1
  have hmr : Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) (ρh x.1.2)) := rmulF_meas _
  have hin : ∀ᵐ a ∂μR, F (stabAct γ (Matrix.of a) x) *
      E.indicator (1 : Mt k r → ℝ≥0∞) (stabAct γ (Matrix.of a) x).1.2 =
      F x * ((Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) (ρh x.1.2)) ⁻¹' A).indicator 1 a := by
    filter_upwards [hstab] with a ha
    rw [hFinv x hx _ ha]
    congr 1
    have h1 := hiff a ha
    show E.indicator (1 : Mt k r → ℝ≥0∞) (fun i j => (Matrix.of a * Matrix.of x.1.2) i j) = _
    by_cases hA' : Formalism.FourierDecayAlt.B.rmulF (n := 2 * r + k + 1) (ρh x.1.2) a ∈ A
    · simp only [Set.indicator_of_mem (h1.mpr hA'), Set.indicator_of_mem (show a ∈ _ ⁻¹' A from hA'),
        Pi.one_apply]
    · simp only [Set.indicator_of_notMem (fun h => hA' (h1.mp h)),
        Set.indicator_of_notMem (show a ∉ _ ⁻¹' A from hA')]
  rw [lintegral_congr_ae hin, lintegral_const_mul _ ((measurable_one.indicator (hmr hA))),
    lintegral_indicator_one (hmr hA), ← Measure.map_apply hmr hA, hR.right _ hρn, mul_comm]

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
