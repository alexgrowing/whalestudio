import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.LocEmb

variable {k r : ℕ}

theorem det_ne_zero_of_mem {g : Mat k r} (hg : g ∈ GG k r) : g.det ≠ 0 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact hH this.symm

theorem isClosed_GG : IsClosed (GG k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem continuousOn_inv : ContinuousOn (fun b : Mat k r => b⁻¹) {b | b.det ≠ 0} := by
  have : (fun b : Mat k r => b⁻¹) = fun b => (b.det)⁻¹ • b.adjugate := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun b hb => hb)
    continuous_id.matrix_adjugate.continuousOn

end GlobalTheory.SgInf.LocEmb

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LocEmb
variable {k r : ℕ}

def quotSet (K : Set (Mt k r)) : Set (Mt k r) :=
  (fun p : Mt k r × Mt k r => ((Matrix.of p.1 : Mat k r) * (Matrix.of p.2 : Mat k r)⁻¹ : Mat k r)) '' (K ×ˢ K)

theorem isCompact_quotSet {K : Set (Mt k r)} (hK : IsCompact K)
    (hd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0) : IsCompact (quotSet K) := by
  refine (hK.prod hK).image_of_continuousOn ?_
  have hc1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have hc2' : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have hc2 : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹) (K ×ˢ K) :=
    continuousOn_inv.comp hc2'.continuousOn fun p hp => hd p.2 hp.2
  exact hc1.continuousOn.mul hc2

end GlobalTheory.SgInf.LocEmb

theorem GlobalTheory.SgInf.lint_compact_le_quot : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r))
    (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS →
    IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F →
    (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  intro k r S μG μS ν K₀ hS hG hSH hU hQ hK₀
  set K : Set (Mt k r) := K₀ ∩ {x | (Matrix.of x : Mat k r) ∈ GG k r} with hKdef
  have hGc : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := LocEmb.isClosed_GG
  have hK : IsCompact K := hK₀.inter_right hGc
  have hKd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0 := fun x hx => LocEmb.det_ne_zero_of_mem hx.2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨μS (LocEmb.quotSet K), (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r S μS hS hSH).1 _ (LocEmb.isCompact_quotSet hK hKd), ?_⟩
  intro F hF hinv

  have hfib : ∀ x : Mt k r, ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
      μS (LocEmb.quotSet K) * F x := by
    intro x
    set A : Set (Mt k r) := {s | (Matrix.of s : Mat k r) ∈ S ∧
      (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K} with hA
    have h1 : ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
        ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := by
      refine lintegral_mono_ae ?_
      have hnull : μS {x | Matrix.of x ∉ S} = 0 := hSH.2.2.1
      filter_upwards [(ae_iff (p := fun s : Mt k r => (Matrix.of s : Mat k r) ∈ S)).2 hnull] with s hs'
      by_cases hsK : (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K
      · rw [Set.indicator_of_mem hsK, Set.indicator_of_mem (show s ∈ A from ⟨hs', hsK⟩)]
        exact le_of_eq (hinv _ hs' x)
      · rw [Set.indicator_of_notMem hsK]; simp
    have h2 : μS A ≤ μS (LocEmb.quotSet K) := by
      rcases A.eq_empty_or_nonempty with hAe | ⟨s₀, hs₀S, hs₀K⟩
      · rw [hAe, measure_empty]; simp
      set t : Mat k r := Matrix.of s₀ with ht
      have htS : t⁻¹ ∈ S := hS.2.2.2.2 _ hs₀S
      have hdx : (Matrix.of x : Mat k r).det ≠ 0 := by
        have := hKd _ hs₀K
        have h' : (Matrix.of (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r) : Mat k r) =
          (Matrix.of s₀ : Mat k r) * Matrix.of x := rfl
        rw [h', Matrix.det_mul] at this
        exact right_ne_zero_of_mul this
      have hsub : A ⊆ rmulM t⁻¹ ⁻¹' LocEmb.quotSet K := by
        intro s ⟨_, hsK⟩
        refine ⟨((fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r),
          (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r)), ⟨hsK, hs₀K⟩, ?_⟩
        show (Matrix.of s : Mat k r) * Matrix.of x * ((Matrix.of s₀ : Mat k r) * Matrix.of x)⁻¹ =
          (Matrix.of s : Mat k r) * t⁻¹
        rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of s : Mat k r),
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdx), Matrix.mul_one]
      calc μS A ≤ μS (rmulM t⁻¹ ⁻¹' LocEmb.quotSet K) := measure_mono hsub
        _ ≤ (μS.map (rmulM t⁻¹)) (LocEmb.quotSet K) :=
          Measure.le_map_apply (continuous_rmulM _).measurable.aemeasurable _
        _ = μS (LocEmb.quotSet K) := by rw [hU.1 _ htS]
    calc _ ≤ ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := h1
      _ ≤ F x * μS A := lintegral_indicator_const_le _ _
      _ ≤ F x * μS (LocEmb.quotSet K) := by gcongr
      _ = μS (LocEmb.quotSet K) * F x := mul_comm _ _
  have hnullG : μG {x | Matrix.of x ∉ GG k r} = 0 := hG.2.2.1
  calc ∫⁻ x in K₀, F x ∂μG = ∫⁻ x, K₀.indicator F x ∂μG :=
        (lintegral_indicator hK₀.isClosed.measurableSet F).symm
    _ ≤ ∫⁻ x, K.indicator F x ∂μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [(ae_iff (p := fun x : Mt k r => (Matrix.of x : Mat k r) ∈ GG k r)).2 hnullG] with x hx'
        by_cases h0 : x ∈ K₀
        · rw [Set.indicator_of_mem h0, Set.indicator_of_mem (show x ∈ K from ⟨h0, hx'⟩)]
        · rw [Set.indicator_of_notMem h0]; simp
    _ = ∫⁻ x, (∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν :=
        hQ _ (hF.indicator hKm)
    _ ≤ ∫⁻ x, μS (LocEmb.quotSet K) * F x ∂ν := lintegral_mono hfib
    _ = μS (LocEmb.quotSet K) * ∫⁻ x, F x ∂ν := lintegral_const_mul _ hF
