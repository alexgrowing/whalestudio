import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftHasSumZeroOfSurjectiveModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
import GroundTheory.PAdicHodge.TiltField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltMultiplicativeExtensionSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulUntiltFrobeniusDoubleSeriesEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBallStatement

noncomputable section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.CoreOrth

theorem core (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [IsAlgClosed F] [CharP F l] [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l])
    (hn : ∀ z, ‖tsh z‖ = ‖z‖) (hs : ∀ x, tsh (ι x) = sh x) (hon : ∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z)
    (h : ℕ) (μ : Fin h → ℂ_[l]) (h2 : 2 ≤ h) (hμ : ∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1)
    (hanti : Antitone (fun i => ‖μ i‖)) (hratio : ∀ i j, ‖μ i‖ < l * ‖μ j‖)
    (horth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) :
    ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧
      (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧
      ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  obtain ⟨-, -, -, -, -, hsurj, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hnι : ∀ x, ‖ι x‖ = ‖sh x‖ := fun x => by rw [← hn, hs]
  choose m hm using fun j => hsurj (μ j) (hμ j).2
  obtain ⟨w, hw⟩ := hsurj (l : ℂ_[l]) (by rw [GlobalTheory.PSer.Laws.norm_l]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  set ϖ : F := ι w with hϖdef
  have hϖ : ‖ϖ‖ = (l : ℝ)⁻¹ := by rw [hnι, hw, GlobalTheory.PSer.Laws.norm_l]
  have hϖs : tsh ϖ = l := by rw [hs, hw]
  set lamF : Fin h → F := fun j => ι (m j) with hlamF
  have hnl : ∀ j, ‖lamF j‖ = ‖μ j‖ := fun j => by simp only [lamF, hnι, hm]
  have hmu : ∀ j, sh (m j) = μ j := hm
  have horthF : GlobalTheory.PMonE.Orth l lamF := by
    intro c j hc
    have := GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal l h m (fun i j => by rw [hmu, hmu]; exact hratio i j) (fun c j => by simp only [hmu]; exact horth c j) c j hc
    have e : (∑ i, (c i : F) * lamF i) = ι (∑ i, (c i : Fl l) * m i) := by simp [lamF, map_sum]
    rw [e, hnι, hnι]; exact this
  have hpos : 0 < h := by omega
  obtain ⟨ρ, τ, K, hρ, hτ, hW1, hW2, hW3⟩ := GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero F l h ϖ hpos hϖ lamF
    (fun j => by rw [← norm_pos_iff, hnl]; exact norm_pos_iff.2 (hμ j).1)
    (fun i j hij => by simp only [hnl]; exact hanti hij) horthF (fun i j => by simp only [hnl]; exact hratio i j)
  set S : Set (Fin h → Fl l) := {x | ∀ j, ‖sh (x j)‖ ≤ ρ j} with hSdef
  let η : (Fin h → Fl l) → Fin h → ℂ_[l] := fun x i => ∑ j, sh (m j) * lam h i (x j)
  have hE : ∀ x ∈ S, ∀ i, ‖η x i - tsh (GlobalTheory.PMonE.rowT l ϖ lamF K (fun j => ι (x j)) i)‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro x hx i
    exact GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow l F ι tsh hn hs hon h m x ϖ K τ i (by omega) hϖs (fun j => (hx j).trans_lt (hρ j).2)
      (fun j n => hW1 (fun j => ι (x j)) (fun j => by rw [hnι]; exact hx j) i j n)
  have hpre : ∀ z : Fin h → F, (∀ j, ‖z j‖ ≤ ρ j) → ∃ x ∈ S, (fun j => ι (x j)) = z := by
    intro z hz
    choose x hx using fun j => hon (z j) ((hz j).trans (hρ j).2.le)
    refine ⟨x, fun j => ?_, funext hx⟩
    rw [← hnι, hx]; exact hz j
  have hL1 : ∀ t : Fin h → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t ht
    choose b hb using fun i => GlobalTheory.T.tiltUntilt_multiplicative_extension_surjective l F ι tsh hn hs hon (t i)
    obtain ⟨z, hz, hrow⟩ := hW2 b (fun i => by rw [← hn, hb]; exact ht i)
    obtain ⟨x, hxS, hxz⟩ := hpre z hz
    refine ⟨x, hxS, fun i => ?_⟩
    have := hE x hxS i
    rwa [hxz, hrow, hb] at this
  obtain ⟨z0, hz0, ⟨j0, hj0⟩, hrow0⟩ := hW3
  obtain ⟨x0, hx0S, hx0z⟩ := hpre z0 hz0
  have hL2 : ∀ i, ‖η x0 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro i
    have := hE x0 hx0S i
    rwa [hx0z, hrow0, map_zero, sub_zero] at this
  obtain ⟨y, hy0, hyS, hysum⟩ := GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fin h → Fl l) (Fin h) η τ S hL1 x0 hx0S hL2
  haveI : Nonempty (Fin h) := ⟨⟨0, hpos⟩⟩
  set R : ℝ := Finset.univ.sup' Finset.univ_nonempty ρ with hRdef
  have hρR : ∀ j, ρ j ≤ R := fun j => Finset.le_sup' ρ (Finset.mem_univ j)
  have hR1 : R < 1 := (Finset.sup'_lt_iff _).2 fun j _ => (hρ j).2
  refine ⟨fun j k => y k j, j0, ρ j0, R, (hρ j0).1.le, (hρ j0).2, hR1,
    fun a k => (hyS k a).trans (hρR a), fun k => hyS k j0, ?_, ?_⟩
  · show ρ j0 ^ l ^ h < ‖sh (y 0 j0)‖
    rw [hy0, ← hnι]
    have := congrFun hx0z j0
    rw [this]; exact hj0
  · intro i
    refine GlobalTheory.T.sum_mul_untiltFrobeniusDoubleSeries_eq_zero l h μ i y R (by omega) hR1 (fun k j => (hyS k j).trans (hρR j)) ?_
    have := hysum i
    simpa [η, hmu] using this

end GlobalTheory.CoreOrth

namespace GlobalTheory.CoreOrth

theorem residue_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → (∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1) → Antitone (fun i => ‖μ i‖) → (∀ i j, ‖μ i‖ < l * ‖μ j‖) → (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) → ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧ (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧ ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  intro l _ h μ h2 hμ hanti hratio horth
  obtain ⟨hac, ι, hs, hon⟩ := GlobalTheory.T.tilt_complexPadic_isAlgClosed_unitBall l
  haveI := hac
  exact core l (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l) ι (GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l) (fun z => GroundTheory.PAdicHodge.norm_tiltSharp z) hs hon
    h μ h2 hμ hanti hratio horth
end GlobalTheory.CoreOrth

end
