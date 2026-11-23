import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem cutSupp (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (K : Set (Mx D a b)) (hK : IsCompact K)
    (Φ : Mx D a b → ℂ) (hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x) (c : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ)
    (hc : HasCompactSupport c) : HasCompactSupport (fun x => c (fun τ i j => compAt θ τ x i j) * Φ x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ)
  obtain ⟨hcl, hcont, -, hcpt⟩ := (GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 a b K hK
  set R' : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin a, ∑ _j : Fin b, R with hR'
  refine HasCompactSupport.intro' (hcpt R') (hcl.inter (isClosed_le hcont continuous_const)) fun x hx => ?_
  by_contra hne
  have hc0 : c (fun τ i j => compAt θ τ x i j) ≠ 0 := left_ne_zero_of_mul hne
  have hΦ : Φ x ≠ 0 := right_ne_zero_of_mul hne
  have hmem : (fun τ i j => compAt θ τ x i j) ∈ Metric.closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ) R :=
    hR (subset_tsupport _ hc0)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  apply hx
  refine ⟨hbox x hΦ, ?_⟩
  show GlobalTheory.Unf.realSize θ x ≤ R'
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := norm_le_pi_norm (fun τ i j => compAt θ τ x i j) τ
  have h2 := norm_le_pi_norm (fun i j => compAt θ τ x i j) i
  have h3 := norm_le_pi_norm (fun j => compAt θ τ x i j) j
  exact h3.trans (h2.trans (h1.trans hmem))

end PositivityTheory.Rg.Rsw.L.LMajor

end
