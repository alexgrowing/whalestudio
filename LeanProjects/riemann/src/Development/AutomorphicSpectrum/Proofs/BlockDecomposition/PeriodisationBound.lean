import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem maj_add_le (θ : InfFam D) (K K₀ : Set (Mx D ρ p)) (N : ℕ) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ R) (g w : Mx D ρ p) (hw : w ∈ K₀) :
    GlobalTheory.Unf.maj θ K N (g + w) ≤ (1 + R) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N g := by
  by_cases hb : GlobalTheory.Unf.InBox K (g + w)
  · have hb' : GlobalTheory.Unf.InBox (K + (-K₀)) g := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨k + -w, Set.add_mem_add hk (Set.neg_mem_neg.2 hw), ?_⟩
      have e : g - (k + -w) = g + w - k := by abel
      rw [e]; exact h0
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h0 := GlobalTheory.Unf.realSize_nonneg θ g
    have h1 := GlobalTheory.Unf.realSize_nonneg θ (g + w)
    have h2 : 1 + GlobalTheory.Unf.realSize θ g ≤ (1 + R) * (1 + GlobalTheory.Unf.realSize θ (g + w)) := by
      have h3 := GlobalTheory.MajSum.realSize_add_le θ (g + w) (-w)
      rw [add_neg_cancel_right] at h3
      have h4 := hR w hw
      nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ g) ^ N := by positivity
    have h5 : (1 + GlobalTheory.Unf.realSize θ g) ^ N ≤ (1 + R) ^ N * (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h2 N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp hq, one_mul]
    exact h5
  · have h0 : GlobalTheory.Unf.maj θ K N (g + w) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N g)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) :
    Continuous (GlobalTheory.Unf.realSize θ : Mx D ρ p → ℝ) := by
  unfold GlobalTheory.Unf.realSize
  refine continuous_finset_sum _ fun τ _ => continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => ?_
  exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ ρ p).matrix_elem i j).norm

theorem periodisation_bound : ∀ {D : D7} {ρ p : ℕ} (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p,
    ∃ B : ℝ, ∀ y : Mx D ρ p,
      Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧
      ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B := by
  intro D ρ p θ hθ φ hφ
  obtain ⟨-, K, hK, hbd⟩ := GlobalTheory.SchwartzMaj.hasMaj_of_mem hθ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ ρ p
  obtain ⟨i1, -, -, -, -, K₀, hK₀, hcov⟩ := lattice_Mx D ρ p
  obtain ⟨C, hC⟩ := hbd N
  have hK' : IsCompact (K + (-K₀)) := hK.add hK₀.neg
  obtain ⟨R₀, hR₀⟩ := hK₀.exists_bound_of_continuousOn (f := fun w => GlobalTheory.Unf.realSize θ (-w))
    ((continuous_realSize hθ).comp continuous_neg).continuousOn
  have hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ |R₀| := fun w hw =>
    (le_abs_self _).trans ((hR₀ w hw).trans (le_abs_self _))
  have hg : Summable fun γ : ratMx D ρ p => GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p) := by
    have h := ENNReal.summable_toReal (hN _ hK')
    refine h.congr fun γ => ?_
    exact ENNReal.toReal_ofReal (GlobalTheory.Unf.maj_nonneg θ _ N _)
  set c : ℝ := |C| * (1 + |R₀|) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c * ∑' γ : ratMx D ρ p, GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p), fun y => ?_⟩
  obtain ⟨γ, hγ, hy⟩ := hcov y
  obtain ⟨ξ₀, rfl⟩ := mem_ratMx.1 hγ
  let e : Matrix (Fin ρ) (Fin p) D.host.E → ratMx D ρ p := fun ξ => ⟨rat (ξ - ξ₀), rat_mem _⟩
  have he : Function.Injective e := fun a b h => by
    have := rat_injective (congrArg Subtype.val h)
    exact sub_left_injective this
  have key : ∀ ξ, ‖φ (rt ξ + y)‖ ≤ c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by
    intro ξ
    have e1 : rt ξ + y = rat (ξ - ξ₀) + (rat ξ₀ + y) := by
      have : rat (ξ - ξ₀) = rt ξ - rat ξ₀ := by
        ext i j
        simp [rat, rt]
      rw [this]; abel
    rw [e1]
    refine (hC _).trans ?_
    have h1 := maj_add_le θ K K₀ N |R₀| (abs_nonneg _) hR (rat (ξ - ξ₀)) (rat ξ₀ + y) hy
    calc C * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y))
        ≤ |C| * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ _ N _)
      _ ≤ |C| * ((1 + |R₀|) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N (rat (ξ - ξ₀))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by rw [hc, mul_assoc]
  have hs' : Summable fun ξ => c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) :=
    (hg.comp_injective he).mul_left c
  have hs : Summable fun ξ => ‖φ (rt ξ + y)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hs'
  refine ⟨hs, (hs.tsum_le_tsum key hs').trans ?_⟩
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  exact tsum_comp_le_tsum_of_inj hg (fun _ => GlobalTheory.Unf.maj_nonneg θ _ N _) he

end GlobalTheory.CompanionTheory.FJE
