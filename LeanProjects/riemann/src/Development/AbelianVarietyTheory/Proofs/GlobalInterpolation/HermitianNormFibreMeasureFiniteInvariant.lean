import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreInvariance

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_act (g : UpqT P Q) (x : Sp P Q) : qf (act g x) = qf x := by
  have hu := GlobalTheory.UpqTopology.mat_unitary g
  apply Complex.ofReal_injective
  rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self]
  show star (UpqT.mat g *ᵥ x) ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ (UpqT.mat g *ᵥ x)) = _
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hu]

theorem normSq_det (g : UpqT P Q) : Complex.normSq (UpqT.mat g).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqTopology.mat_unitary g)
  have hJ : (Formalism.UG.Jpq P Q).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (GlobalTheory.UpqTopology.jpq_sq (P := P) (Q := Q))
    rw [det_mul, h0, zero_mul, det_one] at h1
    exact zero_ne_one h1
  rw [det_mul, det_mul, det_conjTranspose] at h
  have h2 : star (UpqT.mat g).det * (UpqT.mat g).det = 1 := by
    apply mul_right_cancel₀ hJ
    linear_combination h
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, h2, Complex.ofReal_one]

theorem map_volume_act (g : UpqT P Q) :
    (volume : Measure (Sp P Q)).map (act g) = volume := by
  have hdetC : LinearMap.det (Matrix.mulVecLin (UpqT.mat g)) = (UpqT.mat g).det :=
    LinearMap.det_toLin' _
  have hdet : LinearMap.det ((Matrix.mulVecLin (UpqT.mat g)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hdetC, normSq_det]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Sp P Q))
    (f := (Matrix.mulVecLin (UpqT.mat g)).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  exact hmap

theorem continuous_act (g : UpqT P Q) : Continuous (act g : Sp P Q → Sp P Q) :=
  continuous_const.matrix_mulVec continuous_id

private lemma UpqT_mat_mul' (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

private lemma UpqT_mat_one' : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem act_inv_act (g : UpqT P Q) (x : Sp P Q) : act g⁻¹ (act g x) = x := by
  show UpqT.mat g⁻¹ *ᵥ (UpqT.mat g *ᵥ x) = x
  rw [mulVec_mulVec, ← UpqT_mat_mul', inv_mul_cancel, UpqT_mat_one', one_mulVec]

def actHomeo (g : UpqT P Q) : Sp P Q ≃ₜ Sp P Q where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_act g
  right_inv x := by simpa using act_inv_act g⁻¹ x
  continuous_toFun := continuous_act g
  continuous_invFun := continuous_act g⁻¹

theorem act_ne_zero_iff (g : UpqT P Q) (x : Sp P Q) : act g x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · rintro h rfl
    exact h (mulVec_zero _)
  · intro hx h
    apply hx
    rw [← act_inv_act g x, h]
    exact mulVec_zero _

theorem isDxDq_map {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) (g : UpqT P Q) :
    IsDxDq fun t => (fib t).map (act g) := by
  have hm : Measurable (act g) := (continuous_act g).measurable
  have hO : IsOpen {x : Sp P Q | x ≠ 0} := isOpen_ne
  have hU : act g ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} := by
    ext x
    exact act_ne_zero_iff g x
  have hpre : ∀ t : ℝ, act g ⁻¹' (qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0}) =
      qf ⁻¹' {id t} ∩ {x | x ≠ 0} := by
    intro t
    rw [Set.preimage_inter, hU, ← Set.preimage_comp]
    congr 1
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, qf_act]
  have hS : ∀ t : ℝ, MeasurableSet (qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0}) := fun t =>
    (qf_continuous.measurable (measurableSet_singleton _)).inter hO.measurableSet
  have h' : IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fib := h
  obtain ⟨h1, h2, h3⟩ := h'
  show IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fun t => (fib t).map (act g)
  refine ⟨fun t => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · dsimp only
    rw [Measure.map_apply hm (hS t).compl, Set.preimage_compl, hpre t]
    exact h1 t
  · dsimp only
    simp_rw [lintegral_map hφ hm]
    rw [← h2 (fun v => φ (act g v)) (hφ.comp hm)]
    have hdx : (dx P Q).map (act g) = dx P Q := by
      unfold dx
      rw [Measure.map_smul, map_volume_act]
    conv_lhs => rw [← hdx]
    rw [setLIntegral_map hO.measurableSet hφ hm, hU]
  · have hc : Continuous (φ ∘ act g) := hφc.comp (continuous_act g)
    have hs : HasCompactSupport (φ ∘ act g) := hφs.comp_homeomorph (actHomeo g)
    have hU' : tsupport (φ ∘ act g) ⊆ {x | x ≠ 0} := by
      intro x hx
      exact (act_ne_zero_iff g x).1 (hφU (tsupport_comp_subset_preimage φ (continuous_act g) hx))
    obtain ⟨hi, hcont⟩ := h3 _ hc hs hU'
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (integrable_map_measure hφc.aestronglyMeasurable hm.aemeasurable).2 (hi b hb)
    · have he : (fun b => ∫ v, φ v ∂((fib b).map (act g))) = fun b => ∫ v, (φ ∘ act g) v ∂(fib b) := by
        funext b
        exact integral_map hm.aemeasurable hφc.aestronglyMeasurable
      dsimp only
      rw [he]
      exact hcont

theorem fibre_finite_invariant : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β : ℝ), IsDxDq fib →
    β ≠ 0 → IsFiniteMeasureOnCompacts (fib β) ∧
      ∀ g : UpqT P Q, (fib β).map (act g) = fib β := by
  intro P Q fib β h hβ
  have hq : Continuous (qf : Sp P Q → ℝ) := qf_continuous
  have hO : IsOpen {x : Sp P Q | x ≠ 0} := isOpen_ne
  have hz : qf (0 : Sp P Q) = 0 := by simp [qf]
  have hqO : qf ⁻¹' {β} ⊆ {x : Sp P Q | x ≠ 0} := by
    rintro x hx rfl
    apply hβ
    rw [← (hx : qf (0 : Sp P Q) = β), hz]
  refine ⟨⟨fun K hK => ?_⟩, fun g => ?_⟩
  · have h' : IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fib := h
    obtain ⟨h1, -, h3⟩ := h'
    have hb : 0 < |β| := abs_pos.mpr hβ
    have hK' : IsCompact (K ∩ qf ⁻¹' {β}) := hK.inter_right (isClosed_singleton.preimage hq)
    have hT : IsClosed {x : Sp P Q | |qf x| ≤ |β| / 2} :=
      isClosed_le (continuous_abs.comp hq) continuous_const
    have hdisj : Disjoint (K ∩ qf ⁻¹' {β}) {x : Sp P Q | |qf x| ≤ |β| / 2} := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx⟩ hx2
      have hx' : qf x = β := hx
      rw [Set.mem_ofPred_eq, hx'] at hx2
      linarith
    obtain ⟨φ, hφ1, hφ0, hφs, -⟩ := exists_continuous_one_zero_of_isCompact hK' hT hdisj
    have hsupp : tsupport φ ⊆ {x : Sp P Q | x ≠ 0} := by
      have hcl : tsupport φ ⊆ {x : Sp P Q | |β| / 2 ≤ |qf x|} := by
        apply closure_minimal _ (isClosed_le continuous_const (continuous_abs.comp hq))
        intro x hx
        by_contra hc
        have hc' : ¬ (|β| / 2 ≤ |qf x|) := hc
        exact hx (hφ0 (show |qf x| ≤ |β| / 2 from le_of_lt (not_le.mp hc')))
      intro x hx hx0
      have hx2 := hcl hx
      rw [Set.mem_ofPred_eq, hx0, hz, abs_zero] at hx2
      linarith
    obtain ⟨hint, -⟩ := h3 φ φ.continuous hφs hsupp
    have hfin := (hint β (Set.mem_univ β)).lintegral_lt_top
    have hnull : fib β (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ = 0 := h1 β
    have hmeas : Measurable fun x => ENNReal.ofReal (φ x) :=
      ENNReal.measurable_ofReal.comp φ.continuous.measurable
    calc fib β K ≤ fib β ((K ∩ qf ⁻¹' {β}) ∪ (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ) := by
          apply measure_mono
          intro x hx
          by_cases hxS : qf x = β
          · exact Or.inl ⟨hx, hxS⟩
          · exact Or.inr fun hx' => hxS hx'.1
      _ ≤ fib β (K ∩ qf ⁻¹' {β}) + fib β (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ := measure_union_le _ _
      _ = ∫⁻ _ in K ∩ qf ⁻¹' {β}, 1 ∂(fib β) := by rw [hnull, add_zero, setLIntegral_one]
      _ ≤ ∫⁻ x in K ∩ qf ⁻¹' {β}, ENNReal.ofReal (φ x) ∂(fib β) :=
          setLIntegral_mono hmeas fun x hx => by rw [hφ1 hx]; simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib β) := setLIntegral_le_lintegral _ _
      _ < ⊤ := hfin
  · exact GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
      Set.univ _ fib β hq.measurable hO subset_rfl subset_rfl hqO isOpen_univ isOpen_univ
      (Set.mem_univ β) (Set.mem_univ β) (isDxDq_map h g) h

end GlobalTheory.FibreInvariance
