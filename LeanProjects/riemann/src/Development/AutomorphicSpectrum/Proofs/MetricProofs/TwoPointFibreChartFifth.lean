import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirstStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticOrbitOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOneStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_member_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p z hz
  have hV : IsOpen {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} := by
    have hc : Continuous (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) :=
      continuous_pi fun i => continuous_apply _
    exact hUn.preimage hc
  obtain ⟨zex, hzan, hzex⟩ := GlobalTheory.T.two_point_fibre_chart_first K ι Φ y Ψ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hF
  have hbij := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.local_holomorphic_lift_realisation K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
    {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} ΦYn zex z FA.J_top FA.deg_one FA.br_empty hV hz hzan
    (fun u hu => (hzex u hu).1) (fun u hu x₀ hx => ((hzex u hu).2 x₀ hx).1)
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev, hV.mem_nhds hz] with z' h1 hz'
  obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn z')
  obtain ⟨h2, h3, h4⟩ := (hzex z' hz').2 x₀ hx₀
  obtain ⟨hbO, hH⟩ := hF.2.2.2.1 _ hz'
  obtain ⟨hsb, hsd, -, -⟩ := GlobalTheory.T.elementary_factor_properties N j a b ca cb (z' 0) M.j_le hb hab hca hcb
  have hflag : IsBlockDiag j (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) ∧
      (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1).det ≠ 0 := by
    unfold flagAt
    split_ifs with hp
    · subst hp
      refine ⟨(hH p.1).1.mul hsb, ?_⟩
      rw [Matrix.det_mul, hsd, mul_one]
      exact (hH p.1).2
    · exact hH p.1
  have hline := GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ (zex z') (bp (Fin.tail z')) p
    (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) hbO h2 h3 (h4 p.1 p.2) hflag.1 hflag.2
  have hphi : ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
      (FA.S.th (some p)).φ (ΦYn z) (ΦYn z') + FA.S.ph (some p) (ΦYn z') := rfl
  rw [hphi, h1, FA.ref_some, ← hline, hx₀]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
