import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityOfBallPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariablesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVarietyStatement
import Development.WeilBound.CoreStatements.VolumeEquality.ContDiffAtBallPot

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace SheetDecomposition

theorem densU : ∃ κ : ℕ → ℕ → ℕ → ℝ, (∀ f j j', 0 < κ f j j') ∧
    ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), ∀ t ∈ ballDom q,
      maDensity (fun (_ : Fin n) t' => ballPot q t' / 2) t = κ (Fintype.card Ψ) j j' * ballDens q t := by
  have hq : ∀ f j j' : ℕ, Nonempty (Fin f × Fin j × Fin j' ≃ Fin (f * j * j')) := fun f j j' =>
    ⟨Fintype.equivFinOfCardEq (by simp [_root_.mul_assoc])⟩
  choose κ hκ hκ' using fun f j j' : ℕ => GlobalTheory.T.monge_ampere_density_of_ball_potential (Fin f) j j' (f * j * j') (hq f j j').some
  refine ⟨κ, hκ, fun Ψ _ j j' n q t ht => ?_⟩
  obtain rfl : n = Fintype.card Ψ * j * j' := by
    have := Fintype.card_congr q
    simpa [_root_.mul_assoc] using this.symm
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.monge_ampere_density_of_ball_potential Ψ j j' _ q
  rw [hc t ht]
  congr 1
  have h0 := hc 0 (zero_mem_ballDom q)
  have h1 := hκ' (Fintype.card Ψ) j j' 0 (zero_mem_ballDom _)
  rw [ballDens_zero, _root_.mul_one] at h0 h1
  rw [← h0, ← h1]
  obtain ⟨σ, hσ⟩ := ballPot_renumber (Fintype.equivFin Ψ) q (hq (Fintype.card Ψ) j j').some
  have h2 := GlobalTheory.T.monge_ampere_density_change_of_variables _ (fun t' => ballPot (hq (Fintype.card Ψ) j j').some t' / 2) (fun t' => ballPot q t' / 2)
    (fun t i => t (σ i)) (fun _ => 0) 0
    (analyticAt_pi_iff.2 fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (σ i)).analyticAt 0)
    analyticAt_const (contDiffAt_ballPot _ (zero_mem_ballDom _))
    (Eventually.of_forall fun t' => by simp [hσ t'])
  rw [h2, norm_det_perm, one_pow, _root_.one_mul]
  rfl

theorem norm_det_id (n : ℕ) (t : Fin n → ℂ) :
    ‖LinearMap.det ((fderiv ℂ (fun t : Fin n → ℂ => t) t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ = 1 :=
  norm_det_perm (Equiv.refl _) t

theorem transferU : ∃ κ : ℕ → ℕ → ℕ → ℝ, (∀ f j j', 0 < κ f j j') ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ Dc.f Dc.j Dc.j' * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  obtain ⟨κ, hκ, hd⟩ := densU
  refine ⟨κ, hκ, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q G Gk hG hGk hint
  have hdens : ∀ m, ∀ t ∈ Q.V m, maDensity (fun (_ : Fin Dc.n) t' => Real.log ((muLine Hd).h (Q.γ m t'))) t =
      κ Dc.f Dc.j Dc.j' * ballDens (Q.F (Q.pc m)).q t := by
    intro m t ht
    obtain ⟨g, hg, hev⟩ := Q.pot m t ht
    have h2 := GlobalTheory.T.monge_ampere_density_change_of_variables _ (fun t' => ballPot (Q.F (Q.pc m)).q t' / 2)
      (fun t' => Real.log ((muLine Hd).h (Q.γ m t'))) (fun t => t) g t analyticAt_id hg
      (contDiffAt_ballPot _ (Q.V_sub m ht)) hev
    rw [h2, norm_det_id, one_pow, _root_.one_mul]
    exact hd _ _ _ _ _ t (Q.V_sub m ht)
  have hsm : ∀ m, ContDiffOn ℝ 2 (fun t => Real.log ((muLine Hd).h (Q.γ m t))) (Q.V m) := by
    intro m t ht
    obtain ⟨g, hg, hev⟩ := Q.pot m t ht
    have hψ : ContDiffAt ℝ 2 (fun y => (g y).re) t :=
      Complex.reCLM.contDiff.contDiffAt.comp t (hg.contDiffAt.restrict_scalars ℝ)
    exact (((contDiffAt_ballPot _ (Q.V_sub m ht)).add hψ).congr_of_eventuallyEq hev).contDiffWithinAt
  have heq : ∀ m, Set.EqOn
      (fun t => G (Q.γ m t) * maDensity (fun (_ : Fin Dc.n) t' => Real.log ((muLine Hd).h (Q.γ m t'))) t)
      (fun t => κ Dc.f Dc.j Dc.j' * (Gk (Q.pc m) t * ballDens (Q.F (Q.pc m)).q t)) (Q.B m) := by
    intro m t ht
    have hV := (Q.cover.meas m).2 ht
    simp only
    rw [hdens m t hV, hGk m t hV]
    ring
  have hint' : ∀ k, IntegrableOn (fun t => κ Dc.f Dc.j Dc.j' * (Gk k t * ballDens (Q.F k).q t)) (Q.FF k) :=
    fun k => (hint k).const_mul _
  obtain ⟨hs1, hs2⟩ := sum_sheets volume Q.FF Q.pc Q.B Q.d (fun k => (Q.fund k).1) (fun m => (Q.cover.meas m).1)
    Q.B_sub (fun k t => κ Dc.f Dc.j Dc.j' * (Gk k t * ballDens (Q.F k).q t)) Q.count hint'
  have key := GlobalTheory.T.sheet_cover_of_arithmetic_variety K J (mCoordIdeal Dc.y) Dc.n Dc.nCharts Dc.Bd Dc.chart Q.V Q.B Q.γ (muLine Hd) G Dc.arith
    (fun z hz => by
      obtain ⟨a, t, ht, cc, hc, rfl⟩ := Dc.chart_cover z hz
      exact ⟨a, t, ht, _, rfl, cc, hc, rfl⟩)
    Q.cover hsm hG
    (fun m => ((hint' (Q.pc m)).mono_set (Q.B_sub m)).congr_fun (heq m).symm (Q.cover.meas m).1)
    (hs1.congr fun m => setIntegral_congr_fun (Q.cover.meas m).1 fun t ht => congrArg abs (heq m ht).symm)
  refine key.trans ?_
  rw [tsum_congr fun m => setIntegral_congr_fun (Q.cover.meas m).1 (heq m), hs2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

theorem sheet_pieces_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  obtain ⟨κ, hκ, h⟩ := transferU
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q
  exact ⟨κ Dc.f Dc.j Dc.j', hκ _ _ _, h E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q⟩

end SheetDecomposition
