import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddleStatement
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace TopMean

theorem bracket_le (f j' B : ℕ) (rd L : ℝ) (hrd : 2 ≤ rd) (hf : 1 ≤ f) (hj : 1 ≤ j')
    (hB : 2 * f * j' ≤ B) (hB64 : 64 ≤ B) :
    6 + Real.log (2 * (f : ℝ) * rd) + Real.log (2 * (f : ℝ) * j' * rd) ≤
      4 * (Real.log ((B : ℝ) * rd) + |L|) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  have hB' : 2 * (f : ℝ) * j' ≤ B := by exact_mod_cast hB
  have hB64' : (64 : ℝ) ≤ B := by exact_mod_cast hB64
  have hrd0 : 0 < rd := by linarith
  have h1 : Real.log (2 * (f : ℝ) * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_right _ hrd0.le
    nlinarith
  have h2 : Real.log (2 * (f : ℝ) * j' * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right hB' hrd0.le
  have h3 : 3 ≤ Real.log ((B : ℝ) * rd) := by
    have h128 : (128 : ℝ) ≤ (B : ℝ) * rd := by nlinarith
    have hl : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) h128
    have := Real.log_two_gt_d9
    linarith
  have := abs_nonneg L
  linarith

end TopMean

open TopMean in

theorem top_mean_cusp_weight : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  intro hG
  refine ⟨4, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U _ _ hU
  obtain ⟨Q⟩ := GlobalTheory.T.cusp_volume_left hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨κ, hκ, htr⟩ := GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q
  have hw := GlobalTheory.T.cusp_volume_middle E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q U hU
  obtain ⟨hrd, ⟨τ₀⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  intro hj' hN B hB
  have hjN : Dc.j + Dc.j' = Dc.N := by
    have := Dc.j_le; have := Dc.two_le_N
    show Dc.j + (Dc.N - Dc.j) = Dc.N
    omega
  have hball := fun k => GlobalTheory.T.cusp_weight_integrable_on_fundamental_set E (CMType H) Dc.j Dc.j' Dc.n Q.g (Q.Λ k) H (Q.F k) (Q.Γ k) (Q.FF k)
    (Q.arith k) (Q.fund k) hj' (by omega)
  set C : ℝ := (Fintype.card (CMType H) : ℝ) * Dc.j' * (6 + Real.log (2 * Fintype.card (CMType H) * hostRd E) +
    Real.log (2 * Fintype.card (CMType H) * Dc.j' * hostRd E)) with hC
  have hdeg : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t := by
    have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
        ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) (fun _ => 1) := rfl
    rw [e1, htr (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun k => by simpa using (hball k).1)]
    refine congrArg (κ * ·) (Finset.sum_congr rfl fun k _ => ?_)
    simp
  have hnum : ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t :=
    htr U (fun k t => ((Q.F k).R t).cuspW (Q.F k).σ) hw.1 hw.2 (fun k => (hball k).2.2.1)
  have hle : ∀ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t) ≤
      C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) := fun k => by
    have h := mul_le_mul_of_nonneg_left (hball k).2.2.2 (Nat.cast_nonneg (α := ℝ) (Q.d k))
    calc _ ≤ _ := h
      _ = _ := by rw [hC]; ring
  have hDpos : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
    rw [hdeg]
    apply mul_pos hκ
    obtain ⟨k0, hk0⟩ := Q.d_pos
    exact Finset.sum_pos' (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hball k).2.1.le)
      ⟨k0, Finset.mem_univ _, mul_pos (by exact_mod_cast hk0) (hball k0).2.1⟩
  have hmean : meanOf Hd U ≤ C := by
    unfold meanOf
    rw [div_le_iff₀ hDpos, hnum]
    calc κ * ∑ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t)
        ≤ κ * ∑ k, C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) hκ.le
      _ = C * GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
          rw [hdeg, ← Finset.mul_sum]; ring
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hfD : Dc.f = Fintype.card (CMType H) := rfl
  have hN4 : 4 ≤ Dc.N := by omega
  have hB64 : 64 ≤ B := by
    have : 4 * 1 * 4 ^ 2 ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]; gcongr
    omega
  have hB2 : 2 * Fintype.card (CMType H) * Dc.j' ≤ B := by
    have hjN' : Dc.j' ≤ Dc.N ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have : 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]
      calc 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2 := by
            have := Nat.mul_le_mul_left (4 * Fintype.card (CMType H)) hjN'
            nlinarith
        _ = _ := rfl
    omega
  have hbr := bracket_le (Fintype.card (CMType H)) Dc.j' B (hostRd E) (hostLval H) hrd hf hj' hB2 hB64
  have hfj : (0 : ℝ) ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' := by positivity
  calc meanOf Hd U ≤ C := hmean
    _ ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' * (4 * (Real.log ((B : ℝ) * hostRd E) + |hostLval H|)) := by
        rw [hC]; exact mul_le_mul_of_nonneg_left hbr hfj
    _ = 4 * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
        rw [hfD, GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp
