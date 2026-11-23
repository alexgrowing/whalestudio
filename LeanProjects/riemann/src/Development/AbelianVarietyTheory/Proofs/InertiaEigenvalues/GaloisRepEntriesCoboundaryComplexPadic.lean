import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexMatrixGaloisSubgroupApproximaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalisedPeriodAlgebraicEstimateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametricStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInvComplexPadicPeriodMatrixStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem ph_c_cob : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∃ b : ℝ, 0 < b ∧ ∀ (H : Subgroup ↥(GK K)) (t : ℝ), 0 < t → (∀ g ∈ H, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t) → ∀ i j, ∃ y : ℂ_[l], ∀ g ∈ H, ‖Formalism.Per.σC (g : GQ l) y - y - algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j)‖ ≤ b * t ^ 2 := by
  intro l _ n _ _ K ρ M hM
  set Mi : Matrix n n ℂ_[l] := ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) with hMi
  set a : ℝ := 1 + ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) with ha
  have hterm : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) := by
    intro i j
    calc ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ j', (‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖))
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ i)
  have hMa : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg (Mi i j); rw [ha]; linarith
  have hMia : ∀ i j, ‖Mi i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg ((M : Matrix n n ℂ_[l]) i j); rw [ha]; linarith
  have ha0 : 0 < a := by
    rw [ha]; have : 0 ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    linarith
  obtain ⟨c, hc, hAx⟩ := GlobalTheory.T.axLemma_padicComplexMatrix_galoisSubgroup_approximation l
  refine ⟨c * a ^ 2, by positivity, ?_⟩
  intro H t ht hρ i j
  set rC : ↥(GK K) → Matrix n n ℂ_[l] := fun g => (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) with hrCdef
  have hrent : ∀ g : ↥(GK K), ∀ i j, (rC g - 1) i j = algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j) := by
    intro g i j
    have e : rC g - 1 = (algebraMap ℚ_[l] ℂ_[l]).mapMatrix ((ρ g : Matrix n n ℚ_[l]) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]; rfl
  have hrow : ∀ g ∈ H, ∀ i j, ‖(rC g - 1) i j‖ ≤ t := by
    intro g hg i j; rw [hrent, norm_algebraMap']; exact hρ g hg i j
  have hY : ∀ g ∈ H, ∀ i j, ‖(Mi.map (Formalism.Per.σC (g : GQ l)) - Mi) i j‖ ≤ a * t := by
    intro g hg i j
    have hs := GlobalTheory.T.galois_inv_complexPadic_periodMatrix l n K ρ M hM g
    have e : Mi.map (Formalism.Per.σC (g : GQ l)) - Mi = Mi * (rC g - 1) := by
      rw [hMi, hs, mul_sub, mul_one]
    rw [e]
    exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric ℂ_[l] n Mi (rC g - 1) a t ha0.le ht.le hMia (hrow g hg) i j
  obtain ⟨Z, hZ, hZb⟩ := hAx n K H Mi (a * t) (by positivity) hY
  refine ⟨-((M : Matrix n n ℂ_[l]) * Z) i j, fun g hg => ?_⟩
  have hcore := GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul ℂ_[l] n (Formalism.Per.σC (g : GQ l)) (rC g) (M : Matrix n n ℂ_[l]) Mi Z a (c * (a * t)) t
    ha0.le (by positivity) ht.le (GlobalTheory.RingBasics.norm_σC _) (by rw [hMi]; exact M.mul_inv) (hM g) (hZ g hg) hMa hZb (hrow g hg) i j
  rw [hrent] at hcore
  calc _ ≤ t * (a * (c * (a * t))) := hcore
    _ = c * a ^ 2 * t ^ 2 := by ring

end GlobalTheory
