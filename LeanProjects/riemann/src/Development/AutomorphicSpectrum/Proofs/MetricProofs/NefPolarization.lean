import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticVarietyGenericFibreProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericIntersectionEqualsPointsIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GeometricDegreeNonnegativePshStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLatticeShiftNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

theorem exists_ne_zero_of_relevant {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsRelevant (mCoordIdeal y)) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem fin_one_const {α : Type} (a : α) : (fun _ : Fin 1 => a) = ![a] := by
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

namespace GlobalTheory.CompanionTheory.Ar.PB

open GlobalTheory.CompanionTheory.Ar.PB.NefPolProof in

theorem nefPol : NefPol := by
  intro hIn D σ _ S Fl hFl K _ ι _ Ω _ _ y Re hJ hBir I hI n hn
  have hK : Nonempty K := Re.arith.1
  have hRe := GlobalTheory.T.realisation_potential_degree_compatibility hIn.resExists K ι D σ S (mCoordIdeal y) Re
  have hsm : IsSmoothHerm (combLine Re.ref n) := (hRe.2.2.2 n).1
  have hnef : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.NefOnF I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) (combLine Re.ref n).a := by
    intro W hW hle
    obtain ⟨hW', hWmap⟩ := (GlobalTheory.T.arithmetic_variety_generic_fibre_projective K ι 1).1 W hK hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
    have h0 := GlobalTheory.T.geometric_degree_nonnegative_psh hIn K ι D σ S (mCoordIdeal y) Re Fl hFl hJ n hn _ hW' hPW
    have h1 := GlobalTheory.T.generic_intersection_equals_points_integral hIn K ι I hI 1 (W.comap (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ => combLine Re.ref n) hW' (fun _ => hsm)
    rw [hWmap] at h1
    have h2 : (0 : ℝ) ≤ (I W 1 fun _ => (combLine Re.ref n).a : ℤ) := by
      rw [← h1]; exact h0
    rw [← fin_one_const]
    exact_mod_cast h2
  refine ⟨hnef, ?_⟩
  intro hpos β dβ _ _
  have hdeg := (hRe.2.2.2 n).2
  have hgp : 0 < geomDeg (mCoordIdeal y) (combLine Re.ref n) D := by
    rw [hdeg]
    exact mul_pos (by exact_mod_cast Re.deg_pos) hpos
  have h1 := GlobalTheory.T.generic_intersection_equals_points_integral hIn K ι I hI D (mCoordIdeal y) (fun _ => combLine Re.ref n) Re.arith (fun _ => hsm)
  have hI0 : 0 < I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) := by
    have : (0 : ℝ) < (I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) : ℤ) := by
      rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal, ← h1]; exact hgp
    exact_mod_cast this
  have hsec := hIn.siuZ K ι Ω y D (combLine Re.ref n).a I hI Re.arith hBir hnef hI0
  exact GlobalTheory.T.chart_lattice_shift_nonzero K ι Ω y (combLine Re.ref n).a dβ
    (exists_ne_zero_of_relevant y Re.arith.2.1.2.2) hsec

end GlobalTheory.CompanionTheory.Ar.PB
