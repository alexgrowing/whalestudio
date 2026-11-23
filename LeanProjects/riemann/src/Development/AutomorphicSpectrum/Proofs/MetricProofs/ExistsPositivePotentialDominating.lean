import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp

section PosDom
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).of_le two_le_infty).contDiffAt
    (((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
      (P.isOpen_U x)).mem_nhds hy)

theorem isPosPot_rsmul (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (hpos : IsPosPot A P) {c : ℝ} (hc : 0 < c) : IsPosPot A (P.rsmul c) := by
  intro x j y hy w hw
  have h : levi ((P.rsmul c).φ x ∘ (A.chart j).symm) y w =
      c * levi (P.φ x ∘ (A.chart j).symm) y w :=
    TailChernBound.levi_smul' c (potential_contDiffAt A P hP x j hy) w
  rw [h]
  exact mul_pos hc (hpos x j y hy w hw)

theorem isPsh_add_rsmul_succ (A : FinHolAtlas e X) (Θ Φ : LocPot X) (hΘ : IsPotential A Θ)
    (hΘp : IsPosPot A Θ) (hΦ : IsPotential A Φ) (C : ℝ) (hC : IsPsh A (Θ.rsmul C + Φ)) :
    IsPsh A (Φ + LocPot.ofFun (fun _ => 0) + Θ.rsmul (C + 1)) := by
  intro x j y hy w
  have hyΦ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Φ.U x := ⟨hy.1, hy.2.1.1⟩
  have hyΘ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hΘa := potential_contDiffAt A Θ hΘ x j hyΘ
  have hΦa := potential_contDiffAt A Φ hΦ x j hyΦ
  have e1 : (Φ + LocPot.ofFun (fun _ => 0) + Θ.rsmul (C + 1)).φ x ∘ (A.chart j).symm =
      fun z => (C + 1) * (Θ.φ x ∘ (A.chart j).symm) z + 1 * (Φ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Φ.φ x _ + 0 + (C + 1) * Θ.φ x _ = (C + 1) * Θ.φ x _ + 1 * Φ.φ x _
    ring
  have e2 : (Θ.rsmul C + Φ).φ x ∘ (A.chart j).symm =
      fun z => C * (Θ.φ x ∘ (A.chart j).symm) z + 1 * (Φ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show C * Θ.φ x _ + Φ.φ x _ = C * Θ.φ x _ + 1 * Φ.φ x _
    ring
  have h0 := hC x j y ⟨hy.1, hy.2.2, hy.2.1.1⟩ w
  rw [e2, TailChernBound.levi_lin C 1 hΘa hΦa w] at h0
  rw [e1, TailChernBound.levi_lin (C + 1) 1 hΘa hΦa w]
  have h1 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w :=
    TailBoundAlt.isPsh_of_isPosPot A Θ hΘp x j y hyΘ w
  linarith

end PosDom

theorem exists_posPot_dominating : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (Φ : ReciprocityTheory.AnForm.M.LocPot M.Xc), ReciprocityTheory.AnForm.M.IsPotential M.atlas Φ → ∃ Θ : ReciprocityTheory.AnForm.M.LocPot M.Xc, ReciprocityTheory.AnForm.M.IsPotential M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPosPot M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPsh M.atlas (Φ + ReciprocityTheory.AnForm.M.LocPot.ofFun (fun _ => 0) + Θ) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M Φ hΦ
  classical
  obtain ⟨Θ₀, hΘ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K J (mCoordIdeal D.y) D.n M D.A' D.A'_pos.1
  have hpos := GlobalTheory.T.local_section_of_potential_on_model II Ψ K J Ω W D M Θ₀ hΘ₀ hloc
  obtain ⟨C, hC0, hC, -⟩ := ReciprocityTheory.AnForm.P.TailBoundAlt.exists_psh_chern_bound M.atlas Θ₀ Φ hΘ₀ hpos hΦ
  exact ⟨Θ₀.rsmul (C + 1), ReciprocityTheory.AnForm.M.isPotentialRsmul M.atlas (C + 1) Θ₀ hΘ₀,
    isPosPot_rsmul M.atlas Θ₀ hΘ₀ hpos (by linarith),
    isPsh_add_rsmul_succ M.atlas Θ₀ Φ hΘ₀ hpos hΦ C hC⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
