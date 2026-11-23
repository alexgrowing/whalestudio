import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergenceStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquarePolarIntegralIdentityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricFormsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_polar {σ : Type} [Fintype σ] {n : ℕ} {α : Type} {l : Filter α} {f : α → (Fin n → σ) → ℝ}
    {a : (Fin n → σ) → ℝ} (c : Fin n → σ → ℝ) (h : ∀ w, Tendsto (fun t => f t w) l (𝓝 (a w))) :
    Tendsto (fun t => polar n (f t) c) l (𝓝 (polar n a c)) := by
  unfold polar
  exact tendsto_finsetSum _ fun w _ => (h w).const_mul _

theorem Realis.limNum_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type}
    {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) (hpos : 0 < S.t₀) (π : Equiv.Perm (Fin (D + 1)))
    (w : Fin (D + 1) → σ) : Re.limNum II (w ∘ π) = Re.limNum II w := by
  have hev : (fun t => Re.num II t (w ∘ π)) =ᶠ[𝓝[>] 0] fun t => Re.num II t w := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
    have h := (hII.1 K ι).1 P (D + 1) (fun j => Re.line (w j) t) π Re.arith
      fun j => Re.line_smooth _ t ht.1 ht.2
    unfold Realis.num
    exact congrArg (· / (Re.deg : ℝ)) h
  unfold Realis.limNum limUnder
  rw [Filter.map_congr hev]

theorem AnSys.degNum_perm {e : ℕ} {σ : Type} (S : AnSys e σ) (π : Equiv.Perm (Fin e)) (w : Fin e → σ) :
    S.degNum (w ∘ π) = S.degNum w :=
  ReciprocityTheory.AnForm.M.mIntSymm S.A (fun j => S.th (w j)) π fun _ => 1

theorem thmA_limit : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  intro hI hF II hII K _ ι _ d σ _ SY P Re a₀ ε Q c hc u
  have hpos : 0 < SY.t₀ := (SY.reg a₀).1
  have hposW : 0 < Q.an.SW.t₀ := (Q.an.SW.reg none).1
  obtain ⟨C₃, s₀, -, hAg⟩ := GlobalTheory.T.agreement_positive hI (d + 1) σ SY 0 hpos
  have hlim := (hAg II hII K ι P Re).1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ Q.an.SW.t₀ := by
    filter_upwards [Ioc_mem_nhdsGT hposW] with t ht using ⟨ht.1, ht.2⟩
  refine GlobalTheory.T.polar_identity_from_symmetric_forms σ (d + 1) (Re.limNum II) SY.degNum kappa ε a₀ (Re.limNum_perm hII hpos)
    SY.degNum_perm (fun n hn => ?_) c hc u
  have hsq := GlobalTheory.T.square_system_polar_vanishing hI II hII K ι d σ SY P Re a₀ ε Q n hn
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h1 := tendsto_polar (fun _ (x : σ) => (n x : ℝ)) hlim
    have h2 : Tendsto (fun t => polar (d + 2) (Re.num II t) fun _ (x : σ) => (n x : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 := tendsto_polar (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) hlim
    have h2 : Tendsto (fun t => -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i)) (𝓝[>] 0)
        (𝓝 (-∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potH (w r)) Q.an.gH)
          (Q.an.wcoef (fun a => (n a : ℝ)) k i))) :=
      (tendsto_finsetSum _ fun i _ => tendsto_polar _ fun w =>
        (GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q.an w).2).neg
    have h3 := tendsto_nhds_unique (h1.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).2 k hk hk2)) h2
    have h4 := GlobalTheory.T.square_polar_integral_identity hI hF d σ SY a₀ ε Q.an (fun a => (n a : ℝ)) (by simp [hn]) k hk hk2
    rw [h3, h4]
    ring

end GlobalTheory.CompanionTheory.Ar.PB
