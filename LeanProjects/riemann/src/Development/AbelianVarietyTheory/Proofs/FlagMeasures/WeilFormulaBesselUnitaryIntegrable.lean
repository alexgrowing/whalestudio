import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecSmoothAtGapOfDecSmooth

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem measurable_lmul_swap :
    Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
  have hc : Continuous (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    refine continuous_finsetSum _ fun l _ => ?_
    fun_prop
  exact hc.measurable

theorem quotientMeasure_hypotheses_closed_bessel_subgroup {S : Set (Mat k r)} {μG μS ν : Measure (Mt k r)}
    (hS : IsClosedSub k r S) (hG : IsHaarOn (GG k r) μG) (hμS : IsHaarOn S μS)
    (hU : IsUnimod S μS) (hq : IsQuotMeas μG μS ν) :
    PI.QuotientSetting (GG k r) S μG μS ν := by
  obtain ⟨hGm, hGu⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact ⟨hGm, hS.isMatGroup, hS.1, hG, hμS, (hGu μG hG).2, hU.1, hq⟩

theorem eq_map_prod_of_isQuotMeas {μG μS ν : Measure (Mt k r)} [SFinite ν] [SFinite μS]
    (hq : IsQuotMeas μG μS ν) :
    μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
  ext A hA
  have hm := measurable_lmul_swap (k := k) (r := r)
  rw [Measure.map_apply hm hA, ← lintegral_indicator_one hA,
    hq _ (measurable_one.indicator hA), ← lintegral_indicator_one (hm hA),
    lintegral_prod _ ((measurable_one.indicator (hm hA)).aemeasurable)]
  rfl

theorem weil_integrable :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S →
      IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν →
      SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧
      μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧
      (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B),
        Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧
          ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧
      (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) →
        ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  intro k r S μG μS ν hS hG hμS hU hq
  have hset := quotientMeasure_hypotheses_closed_bessel_subgroup hS hG hμS hU hq
  have : SigmaFinite μS := hμS.1
  have : SigmaFinite μG := hG.1
  have hm := measurable_lmul_swap (k := k) (r := r)

  obtain ⟨f0, hf0pos, hf0m, hf0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG one_ne_zero
  set g : Mt k r → ENNReal := fun x => ∫⁻ s, (f0 (lmulM (Matrix.of s) x) : ENNReal) ∂μS with hg
  have hgm : Measurable g := by
    have : Measurable (fun p : Mt k r × Mt k r => (f0 (lmulM (Matrix.of p.2) p.1) : ENNReal)) :=
      (measurable_coe_nnreal_ennreal.comp hf0m).comp hm
    exact this.lintegral_prod_right'
  have hgpos : ∀ x, 0 < g x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have hmx : Measurable (fun s : Mt k r => (f0 (lmulM (Matrix.of s) x) : ENNReal)) :=
      (measurable_coe_nnreal_ennreal.comp hf0m).comp (hm.comp measurable_prodMk_left)
    change ∫⁻ s, (f0 (lmulM (Matrix.of s) x) : ENNReal) ∂μS = 0 at h0
    rw [lintegral_eq_zero_iff hmx] at h0
    have hall : ∀ᵐ s ∂μS, False := by
      filter_upwards [h0] with s hs
      simp only [Pi.zero_apply, ENNReal.coe_eq_zero] at hs
      exact (hf0pos _).ne' hs
    exact hμS.2.1 (Measure.measure_univ_eq_zero.mp (by simpa using hall))
  have hgint : ∫⁻ x, g x ∂ν < ⊤ := by
    have := hq (fun x => (f0 x : ENNReal)) (measurable_coe_nnreal_ennreal.comp hf0m)
    have h2 : ∫⁻ x, g x ∂ν = ∫⁻ x, (f0 x : ENNReal) ∂μG := by rw [this]; rfl
    rw [h2]
    exact hf0int.trans ENNReal.one_lt_top

  have hsig : SigmaFinite ν := by
    refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ENNReal) + 1)⁻¹ ≤ g x})
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      have hne : ((n : ENNReal) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
      have hnt : ((n : ENNReal) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp)
      calc ν {x | ((n : ENNReal) + 1)⁻¹ ≤ g x} ≤ (∫⁻ x, g x ∂ν) / ((n : ENNReal) + 1)⁻¹ :=
            meas_ge_le_lintegral_div hgm.aemeasurable hne hnt
        _ < ⊤ := ENNReal.div_lt_top hgint.ne hne
    · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
      intro x
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hgpos x).ne'
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      show ((n : ENNReal) + 1)⁻¹ ≤ g x
      refine le_trans ?_ hn.le
      exact ENNReal.inv_le_inv.mpr le_self_add
  have hmap := eq_map_prod_of_isQuotMeas (μG := μG) (μS := μS) (ν := ν) hq
  refine ⟨hsig, ?_, hmap, ?_, ?_⟩
  · have hae := GlobalTheory.QuotRightInv.ae_mem_of_quot hset
    rw [ae_iff] at hae
    simpa using hae
  · intro B _ _ _ f hf
    rw [hmap] at hf
    have hf' : Integrable (fun p : Mt k r × Mt k r => f (lmulM (Matrix.of p.2) p.1)) (ν.prod μS) :=
      (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hf
    refine ⟨hf'.integral_prod_left, ?_⟩
    rw [hmap, integral_map hm.aemeasurable hf.aestronglyMeasurable, integral_prod _ hf']
  · intro F hF hFS y hy
    exact GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset F hF (fun s hs x _ => hFS s hs x) y hy

end GlobalTheory.SgInf
