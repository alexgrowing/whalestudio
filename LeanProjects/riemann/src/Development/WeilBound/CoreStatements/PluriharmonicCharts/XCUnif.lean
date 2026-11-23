import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtDetFac
import Development.WeilBound.CoreStatements.PluriharmonicCharts.NotMemOfEqTop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace PositivityTheory.Xgp.c_unif

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem chart_over (FA : FlagAn BM d) (x : FA.S.X) {l : Fin BM.q} (hl : FA.pr x ∈ BM.O l \ bdry BM.s)
    {Vb : Set BM.Rb.X} {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hVb : FA.pr x ∈ Vb)
    (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) :
    ∃ V g, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V g ∧
      ((∀ k, FA.pr x ∈ (BM.Rb.A.chart k).source → ∀ v : Fin n → ℂ,
        (∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * Matrix.of fun a b =>
          fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart k).symm w) a b) (BM.Rb.A.chart k (FA.pr x)) v) a b = 0) → v = 0) →
        IsFlagImmersionAt (FA.S.comap some).A g x) := by
  have hb := GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA
  have hd := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hd
  obtain ⟨σ, h1, h2, hσ, hinj⟩ := exists_inv FA.S.A FA.Re.R.A FA.Re.π FA.Re.holo hd hb
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary n _ BM.Rb.A BM.L BM.s BM.sec
  have hW : IsOpen (σ ⁻¹' FA.Re.R.U (σ x) ∩ FA.pr ⁻¹' ((BM.O l \ bdry BM.s) ∩ Vb)) :=
    ((FA.Re.R.isOpen_U _).preimage hσ.1).inter ((((BM.O_open l).sdiff hcl).inter hPi.1).preimage FA.pr_holo.1)
  have hcomp : ∀ x', σ x' ∈ FA.Re.R.U (σ x) → SameOrbit (FA.Re.R.lift (σ x) (σ x')) (FA.Re.R.lift (σ x') (σ x')) :=
    fun x' h => FA.Re.R.compat _ _ _ ⟨h, FA.Re.R.mem_U _⟩
  obtain ⟨W, hWo, hxW, hsub, h₀, L, hh₀, hL, hLb, ho⟩ := exists_holo_flags BM FA.pr_holo hW
    (z := fun x' => FA.Re.R.lift (σ x) (σ x'))
    (fun q => holoOn_mono (holoOn_comp hσ (FA.Re.R.holo (σ x) q)) Set.inter_subset_left)
    (fun x' h => FA.Re.R.mem _ _ h.1)
    (fun x' h => orbit_trans (Fib.sameOrbit_basePart M.blk (hcomp x' h.1)) (by
      have := FA.pr_eq (σ x')
      rwa [h1] at this))
    (l := l) (fun x' h => h.2.1.1) (x₀ := x) ⟨FA.Re.R.mem_U _, hl, hVb⟩
  obtain ⟨V, hV⟩ := period_chart FA hb.2 hPi hWo hxW (fun x' h => (hsub h).2) (H := fun τ x' => h₀ τ * L τ x')
    (fun τ => holoOn_mul (fun _ _ _ => analyticOnNhd_const) (hL τ))
    (fun τ x' _ => ⟨(hh₀ τ).1.mul (hLb τ x').1, by
      rw [Matrix.det_mul, (hLb τ x').2.det, mul_one]; exact (hh₀ τ).2⟩)
    (fun x' h x₀ e => by
      have e' : x₀ = σ x' := by rw [← e, h2]
      rw [e']
      exact orbit_trans (orbit_symm (hcomp x' (hsub h).1)) (ho x' h))
  exact ⟨V, _, hV, fun himm => flag_immersion FA hσ hinj hPi hWo hxW hl.1 hVb hh₀ hL hLb ho himm⟩

theorem exists_over (FA : FlagAn BM d) {l : Fin BM.q} {b : BM.Rb.X} (hb : b ∈ BM.O l) : ∃ x, FA.pr x = b := by
  obtain ⟨x₀, hx₀⟩ := FA.Re.R.surj _ (GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l b hb (fun _ => 1)
    fun _ => ⟨isBlockDiag_one, by simp⟩) (not_mem_of_eq_top FA.J_top _)
  refine ⟨FA.Re.π x₀, BM.Rb.inj _ _ (not_mem_of_eq_top rfl _) ?_⟩
  have h := Fib.sameOrbit_basePart M.blk hx₀
  rw [FC.basePart_flagPt] at h
  exact orbit_trans (orbit_symm (FA.pr_eq x₀)) (orbit_trans h (GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l b hb).2.2.2)

theorem mem_open_iff (FA : FlagAn BM d) (x : FA.S.X) : x ∈ (FA.S.comap some).open' ↔ FA.pr x ∉ bdry BM.s := by
  show ¬ FA.S.s x x = 0 ↔ _
  rw [FA.s_eq]
  rfl

end PositivityTheory.Xgp.c_unif
