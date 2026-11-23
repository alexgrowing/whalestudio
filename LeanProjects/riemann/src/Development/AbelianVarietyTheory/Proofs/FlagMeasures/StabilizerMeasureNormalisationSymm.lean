import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalFormStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabMeas

variable {k r : ℕ}

theorem cont_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem meas_conj (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) :=
  (cont_conj a).measurable

theorem meas_lmul (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) :=
  (cont_lmul a).measurable

theorem conj_conj (a b : Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show a * (b * Matrix.of x * b⁻¹) * a⁻¹ = a * b * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem conj_one (x : Mt k r) : conjM 1 x = x := by
  show (1 : Mat k r) * Matrix.of x * 1⁻¹ = Matrix.of x
  simp

theorem map_conj_conj (a b : Mat k r) (μ : Measure (Mt k r)) :
    (μ.map (conjM b)).map (conjM a) = μ.map (conjM (a * b)) := by
  rw [Measure.map_map (meas_conj a) (meas_conj b), conj_conj]

def conjEquiv {a : Mat k r} (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have := congrFun (conj_conj a⁻¹ a) x
    rw [Matrix.nonsing_inv_mul _ ha, conj_one] at this
    exact this
  right_inv x := by
    have := congrFun (conj_conj a a⁻¹) x
    rw [Matrix.mul_nonsing_inv _ ha, conj_one] at this
    exact this
  measurable_toFun := meas_conj a
  measurable_invFun := meas_conj a⁻¹

theorem conj_back {a : Mat k r} (ha : IsUnit a.det) (s : Mat k r) : a * (a⁻¹ * s * a) * a⁻¹ = s := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ ha]

theorem haar_conj {a : Mat k r} (ha : IsUnit a.det) {S S' : Set (Mat k r)} (hS : ∀ x, a * x * a⁻¹ ∈ S' ↔ x ∈ S)
    {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) :
    IsHaarOn S' (μ.map (conjM a)) ∧ IsUnimod S' (μ.map (conjM a)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  have hb : ∀ s ∈ S', a⁻¹ * s * a ∈ S := fun s hs => (hS _).1 (by rwa [conj_back ha])
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact (conjEquiv ha).measurableEmbedding.sigmaFinite_map
  · intro h0
    exact h2 ((Measure.map_eq_zero_iff (meas_conj a).aemeasurable).1 h0)
  · have := (conjEquiv ha).map_apply (μ := μ) {x | Matrix.of x ∉ S'}
    refine this.trans ?_
    rw [← h3]
    congr 1
    ext x
    exact not_congr (hS (Matrix.of x))
  · conv_rhs => rw [← h4 _ (hb s hs)]
    rw [Measure.map_map (meas_lmul _) (meas_conj a), Measure.map_map (meas_conj a) (meas_lmul _)]
    congr 1
    funext x
    show s * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * s * a * Matrix.of x) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ha]
  · conv_rhs => rw [← h5 _ (hb s hs)]
    rw [Measure.map_map (continuous_rmulM _).measurable (meas_conj a),
      Measure.map_map (meas_conj a) (continuous_rmulM _).measurable]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹) * s = a * (Matrix.of x * (a⁻¹ * s * a)) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
  · conv_rhs => rw [← h6]
    rw [Measure.map_map measurable_invM (meas_conj a), Measure.map_map (meas_conj a) measurable_invM]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹)⁻¹ = a * (Matrix.of x)⁻¹ * a⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]

theorem haar_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) {s : ℝ} (hs : 0 < s) :
    IsHaarOn S (ENNReal.ofReal s • μ) ∧ IsUnimod S (ENNReal.ofReal s • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact inferInstanceAs (SigmaFinite (s.toNNReal • μ))
  · intro h0
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      ENNReal.ofReal_eq_zero, Measure.measure_univ_eq_zero] at this
    rcases this with h | h
    · exact absurd h (not_le.2 hs)
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul, h4 s hs]
  · rw [Measure.map_smul, h5 s hs]
  · rw [Measure.map_smul, h6]

theorem isClosedSub_Rset {γ : Mat k r} (hγ : γ ∈ GG k r) : IsClosedSub k r (Rset k r γ) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG hγ
  refine ⟨fun x hx => n1 hx.1, ?_, ⟨n3, ?_⟩, fun a ha b hb => ⟨n4 _ ha.1 _ hb.1, ?_⟩, fun a ha => ⟨n5 _ ha.1, ?_⟩⟩
  · have hc : Continuous fun x : Mat k r => γ * x * γ⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := n2.inter (n2.preimage hc)
    exact this
  · rwa [Matrix.mul_one, Matrix.mul_nonsing_inv _ hu]
  · convert n4 _ ha.2 _ hb.2 using 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · convert n5 _ ha.2 using 1
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc]

theorem conj_mem_Nset {n : Mat k r} (hn : n ∈ Nset k r) (x : Mat k r) : n * x * n⁻¹ ∈ Nset k r ↔ x ∈ Nset k r := by
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG (n1 hn)
  refine ⟨fun h => ?_, fun h => n4 _ (n4 _ hn _ h) _ (n5 _ hn)⟩
  convert n4 _ (n4 _ (n5 _ hn) _ h) _ hn using 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem conj_mem_Rset {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g x : Mat k r) :
    n₂⁻¹ * x * n₂⁻¹⁻¹ ∈ Rset k r (n₁ * g * n₂) ↔ x ∈ Rset k r g := by
  have hu := isUnit_det_of_mem_GG (isClosedSub_Nset.1 h₂)
  have e : n₁ * g * n₂ * (n₂⁻¹ * x * n₂⁻¹⁻¹) * (n₁ * g * n₂)⁻¹ = n₁ * (g * x * g⁻¹) * n₁⁻¹ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  show (_ ∧ _) ↔ (_ ∧ _)
  rw [e, conj_mem_Nset h₁, conj_mem_Nset (isClosedSub_Nset.2.2.2.2 _ h₂)]

theorem dmin_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r z z' (n₁ * g * n₂) l = Dmin k r z z' g l :=
  Formalism.QuantumDeterminants.dInv k r z z' hz hz' n₁ ⟨1, (isClosedSub_UWset z).2.2.1, n₁, h₁, (Matrix.one_mul _).symm⟩
    n₂ ⟨1, (isClosedSub_UWset z').2.2.1, n₂, h₂, (Matrix.one_mul _).symm⟩ g l

theorem stabilizer_measure_normalisation : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → γ ∈ GG k r ∧ IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ s (μR.map (conjM γ)) ∧ 0 < Dj k r hj z z' γ ∧ Dj k r hj z' z γ⁻¹ = Dj k r hj z z' γ ∧ ∀ De, DeOK k r z z' γ De → DeOK k r z' z γ⁻¹ De := by
  rintro k r j hj z z' γ s μR hs ⟨hz, hz', hT, n₁, h₁, n₂, h₂, g₀, β, c, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g₀ β c hz hz' hT hg
  obtain ⟨b1, b2⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg
  have c1 := GlobalTheory.T.map_conj_lebesgueCommonStabilizerNormalForm k r j hj z z' g₀ β c hz hz' hT hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  have hD : ∀ l, ‖Dmin k r z' z (n₁ * g₀ * n₂)⁻¹ l‖ = ‖Dmin k r z z' (n₁ * g₀ * n₂) l‖ := fun l => by
    rw [hinv, dmin_N hz' hz (n5 _ h₂) (n5 _ h₁), dmin_N hz hz' h₁ h₂, a6]
  refine ⟨hγ, isClosedSub_Rset hγ, e1, e2,
    ⟨hz', hz, a1 ▸ hT, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, c⁻¹, a3, hinv, ?_⟩, ?_, hD _, fun De h => ⟨h.1, ?_⟩⟩
  · rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
      Measure.map_smul, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]
  · unfold Dj at a4 ⊢
    rwa [dmin_N hz hz' h₁ h₂]
  · intro l hl h0
    rw [hD]
    refine h.2 l hl fun h' => h0 ?_
    rw [← norm_eq_zero, hD, h', norm_zero]

end GlobalTheory.Amp.StabMeas
