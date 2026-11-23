import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.LowestKTypeUnitIntegral

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.MainNotions.BridgeCSchur

variable {n : ℕ}

theorem exists_lowK_unit {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)} (hσ : IsDS ε lam σ) :
    ∃ v ∈ lowKSub ε lam σ, ‖v‖ = 1 := by
  obtain ⟨S, hS⟩ := hσ.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hle : S ≤ lowKSub ε lam σ := le_sSup hS
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, Submodule.smul_mem _ _ (hle hvS), ?_⟩
  rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]

theorem coef_int {ε' : Fin n → Bool} {mu : Fin n → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (h2 : 2 ≤ n) (hc : Formalism.QuantumDeterminants.IsHCParam mu)
    (hσ : IsDS ε' mu σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)) (ν : Measure (UJ ε'))
    [ν.IsHaarMeasure] {w : K} (hw : w ∈ lowKSub ε' mu σ) (hw1 : ‖w‖ = 1) :
    Integrable (fun h : UJ ε' => ⟪w, σ (um h) w⟫_ℂ) ν := by
  obtain ⟨-, hDec, hInt, -⟩ := CompanionTheory.Lime.T3.analytic_estimates
  have h1 := hDec n (n + 1) ε' mu K σ (by omega) (by omega) hc hσ (by push_cast; exact hg) w hw hw1 1 _ le_rfl
  have e1 : σ (um (1 : UJ ε')) w = w := by
    rw [show um (1 : UJ ε') = 1 from rfl, hσ.2.2.1.1.1]; rfl
  rw [e1] at h1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have h2' : (n : ℝ) ^ 2 + 1 ≤ 6 * ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith
  exact (hInt n ε' ν inferInstance (by omega) _ _ _ (continuous_const.inner ((uRep_self hσ.2.2.1).cont w)) h2' h1).1

theorem inv_inv_of_haar {m : ℕ} {ε : Fin m → Bool} (ν : Measure (UJ ε)) [ν.IsHaarMeasure] : ν.IsInvInvariant := by
  rw [Measure.isMulLeftInvariant_eq_smul ν (muG ε)]
  exact ⟨by rw [Measure.inv, Measure.map_smul]; exact congrArg _ (Measure.inv_eq_self (muG ε))⟩

theorem of_integral_holds : OfInt := by
  intro n ε lam ε' mu e hG H H' _ _ _ _ _ _ π σ ν hν hπ hσ w hw hw1 a b hI
  haveI := hν
  obtain ⟨κ, -, hS⟩ := schur_haar hσ ν
  have hm := coef_int hG.two hG.hc' hσ hG.gap' ν hw hw1
  obtain ⟨j, hj1, hj2⟩ := exists_intertwiner ν (uRep_emb hG.fits hπ.2.2.1) (uRep_self hσ.2.2.1)
    (irr_of hσ.2.2.2.1) κ (fun v w v' w' => (hS v w v' w').2) w (norm_ne_zero_iff.1 (by rw [hw1]; exact one_ne_zero)) hm a
  refine ⟨j, fun h0 => hI ?_, hj1⟩
  rw [← hj2 b, h0]
  simp

end PositivityTheory.RgHe.LowestKTypeUnitIntegral
