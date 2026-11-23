import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.FormalDegreeBessel.FinalG
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftErrorLocal

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def phi (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (u : UJ ε) : Mt k r :=
  (P⁻¹ * ((u : (Mat k r)ˣ) : Mat k r) * P : Mat k r)

variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}

lemma conj_mul (hP : IsUnit P.det) (U V : Mat k r) :
    (P⁻¹ * U * P) * (P⁻¹ * V * P) = P⁻¹ * (U * V) * P := by
  have h : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  calc (P⁻¹ * U * P) * (P⁻¹ * V * P) = P⁻¹ * U * (P * P⁻¹) * V * P := by simp only [Matrix.mul_assoc]
    _ = P⁻¹ * (U * V) * P := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma conj_back (hP : IsUnit P.det) (U : Mat k r) : P * (P⁻¹ * U * P) * P⁻¹ = U := by
  have h : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  calc P * (P⁻¹ * U * P) * P⁻¹ = (P * P⁻¹) * U * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [h, Matrix.one_mul, Matrix.mul_one]

lemma conj_back' (hP : IsUnit P.det) (U : Mat k r) : P⁻¹ * (P * U * P⁻¹) * P = U := by
  have h : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  calc P⁻¹ * (P * U * P⁻¹) * P = (P⁻¹ * P) * U * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [h, Matrix.one_mul, Matrix.mul_one]

lemma lmul_phi (hP : IsUnit P.det) (u v : UJ ε) : lmulM (phi ε P u) (phi ε P v) = phi ε P (u * v) :=
  conj_mul hP _ _

lemma rmul_phi (hP : IsUnit P.det) (u v : UJ ε) : rmulF (phi ε P u) (phi ε P v) = phi ε P (v * u) :=
  conj_mul hP _ _

lemma phi_closedEmbedding (hE : UJEmb) (hP : IsUnit P.det) : IsClosedEmbedding (phi ε P) := by
  have h1 : IsClosedEmbedding (fun x : Mat k r => P⁻¹ * x * P) :=
    Function.LeftInverse.isClosedEmbedding (f := fun x : Mat k r => P * x * P⁻¹) (fun x => conj_back hP x)
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  exact h1.comp (hE _ ε).1

lemma phi_measurable (hE : UJEmb) (hP : IsUnit P.det) : Measurable (phi ε P) :=
  (phi_closedEmbedding hE hP).continuous.measurable

lemma phi_range_iff (hE : UJEmb) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r) (g : Mat k r) :
    (∃ u, phi ε P u = g) ↔ g ∈ GV k r := by
  constructor
  · rintro ⟨u, hu⟩
    have : (P⁻¹ * ((u : (Mat k r)ˣ) : Mat k r) * P : Mat k r) = g := hu
    rw [← this]
    refine (hC _ ε _ P hP hH _).2 ?_
    rw [conj_back hP]
    exact u.2
  · intro hg
    have h1 : inUJ ε (P * g * P⁻¹) := (hC _ ε _ P hP hH g).1 hg
    have h2 : P * g * P⁻¹ ∈ Set.range (fun g : UJ ε => ((g : (Mat k r)ˣ) : Mat k r)) := by
      rw [(hE _ ε).2]; exact h1
    obtain ⟨u, hu⟩ := h2
    refine ⟨u, ?_⟩
    show P⁻¹ * _ * P = g
    have hu' : ((u : (Mat k r)ˣ) : Mat k r) = P * g * P⁻¹ := hu
    rw [hu', conj_back' hP]

lemma phi_range (hE : UJEmb) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r) :
    Set.range (phi ε P) = GV k r := Set.ext fun g => phi_range_iff hE hC hP hH g

lemma lmul_cont (a : Mat k r) : Continuous (lmulM a) := by
  have : Continuous (fun x : Mat k r => a * x) := continuous_const.matrix_mul continuous_id
  exact this

lemma rmul_cont (a : Mat k r) : Continuous (rmulF a) := by
  have : Continuous (fun x : Mat k r => x * a) := continuous_id.matrix_mul continuous_const
  exact this

theorem haar_map (hE : UJEmb) (hU : Unimodular) (hC : UHConj) (hP : IsUnit P.det)
    (hH : Pᴴ * Jm ε * P = Hpk k r) : IsHaarOn (GV k r) ((muG ε).map (phi ε P)) := by
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hr := phi_range hE hC hP hH
  have hcl : IsClosed (Set.range (phi ε P)) := hce.isClosed_range
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr, Measure.map_apply hm hcl.measurableSet.compl]
    have : phi ε P ⁻¹' (Set.range (phi ε P))ᶜ = ∅ := by
      ext u; simp
    rw [this, measure_empty]
  · intro a ha
    rw [← hr] at ha
    obtain ⟨u, rfl⟩ := ha
    have hl : Measurable (lmulM (phi ε P u)) := (lmul_cont _).measurable
    rw [Measure.map_map hl hm]
    have e : lmulM (phi ε P u) ∘ phi ε P = phi ε P ∘ (fun v => u * v) := by
      funext v; exact lmul_phi hP u v
    rw [e, ← Measure.map_map hm (measurable_const_mul u), map_mul_left_eq_self]
  · intro a ha
    rw [← hr] at ha
    obtain ⟨u, rfl⟩ := ha
    have hl : Measurable (rmulF (phi ε P u)) := (rmul_cont _).measurable
    rw [Measure.map_map hl hm]
    have e : rmulF (phi ε P u) ∘ phi ε P = phi ε P ∘ (fun v => v * u) := by
      funext v; exact rmul_phi hP u v
    rw [e, ← Measure.map_map hm (measurable_mul_const u), hU]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    exact (hce.isCompact_preimage hK).measure_lt_top
  · intro h0
    have h1 : ((muG ε).map (phi ε P)) Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.measure_univ_eq_zero] at h1
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := muG ε)).open_pos Set.univ isOpen_univ ⟨1, trivial⟩ (by rw [h1]; rfl)

theorem haar_unique (hE : UJEmb) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r)
    (ν : Measure (Mt k r)) (hν : IsHaarOn (GV k r) ν) : ∃ c : ℝ≥0, ν = c • (muG ε).map (phi ε P) := by
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hme : MeasurableEmbedding (phi ε P) := hce.measurableEmbedding
  have hr := phi_range hE hC hP hH
  have hfin : IsFiniteMeasureOnCompacts (ν.comap (phi ε P)) := ⟨fun K hK => by
    rw [hme.comap_apply]
    exact hν.finite_compact _ (hK.image hce.continuous)⟩
  have hinv : (ν.comap (phi ε P)).IsMulLeftInvariant := ⟨fun u => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul u) hs, hme.comap_apply, hme.comap_apply]
    have hu : Matrix.of (phi ε P u) ∈ GV k r := (phi_range_iff hE hC hP hH _).1 ⟨u, rfl⟩
    have h1 := hν.left _ hu
    have hs' : MeasurableSet (phi ε P '' s) := hme.measurableSet_image.2 hs
    conv_rhs => rw [← h1, Measure.map_apply (lmul_cont _).measurable hs']
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨u * w, hw, (lmul_phi hP u w).symm⟩
    · rintro ⟨v, hv, hx⟩
      refine ⟨u⁻¹ * v, by simpa using hv, ?_⟩
      have h2 : lmulM (phi ε P u⁻¹) (lmulM (phi ε P u) x) = x := by
        have h3 : (Matrix.of (phi ε P u⁻¹) : Mat k r) * Matrix.of (phi ε P u) = 1 := by
          have := lmul_phi hP u⁻¹ u
          rw [inv_mul_cancel] at this
          refine Eq.trans this ?_
          show P⁻¹ * (1 : Mat k r) * P = 1
          rw [Matrix.mul_one, Matrix.nonsing_inv_mul P hP]
        show (Matrix.of (phi ε P u⁻¹) : Mat k r) * (Matrix.of (phi ε P u) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      rw [← lmul_phi hP, hx]; exact h2⟩
  refine ⟨Measure.haarScalarFactor (ν.comap (phi ε P)) (muG ε), ?_⟩
  have h1 := Measure.isMulLeftInvariant_eq_smul (ν.comap (phi ε P)) (muG ε)
  have h2 : (ν.comap (phi ε P)).map (phi ε P) = ν := by
    rw [hme.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    have := hν.conc
    rw [← hr] at this
    exact this
  rw [← Measure.map_smul, ← h1, h2]

lemma hs_eq_gN (g : Mat k r) : hs g = gN g ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have h1 : gN g ^ 2 = ∑ i, ∑ j, Complex.normSq (g i j) := Real.sq_sqrt h0
  rw [h1]
  unfold hs
  simp only [Complex.normSq_eq_norm_sq]

lemma hs_nonneg' (g : Mat k r) : 0 ≤ hs g := by rw [hs_eq_gN]; positivity

theorem vol_crude (hE : UJEmb) (hV : VolGrowth) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r)
    (ν : Measure (Mt k r)) (hν : IsHaarOn (GV k r) ν) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ν {g | gN (Matrix.of g) ≤ R} ≤
      ENNReal.ofReal (C * R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨c, rfl⟩ := haar_unique hE hC hP hH ν hν
  obtain ⟨C, hCV⟩ := hV _ ε
  have hm := phi_measurable (ε := ε) hE hP
  set M : ℝ := 1 + hs P * hs P⁻¹ with hM
  have hM0 : 0 ≤ hs P * hs P⁻¹ := mul_nonneg (hs_nonneg' _) (hs_nonneg' _)
  have hM1 : 1 ≤ M := by linarith
  refine ⟨c * (C * M ^ (2 * (2 * r + k + 1) ^ 2)), fun R hR => ?_⟩
  have hms : MeasurableSet {g : Mt k r | gN (Matrix.of g) ≤ R} := by
    have : Measurable fun g : Mt k r => gN (Matrix.of g) := by
      unfold gN
      apply Measurable.sqrt
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      have : Measurable fun g : Mt k r => g i j := (measurable_pi_apply j).comp (measurable_pi_apply i)
      exact Complex.continuous_normSq.measurable.comp this
    exact this measurableSet_Iic
  rw [Measure.smul_apply, Measure.map_apply hm hms, ENNReal.smul_def, smul_eq_mul]
  have hsub : phi ε P ⁻¹' {g : Mt k r | gN (Matrix.of g) ≤ R} ⊆ {u : UJ ε | hsG u ≤ (M * R) ^ 2} := by
    intro u hu
    have hu' : gN (Matrix.of (phi ε P u)) ≤ R := hu
    have h0 : 0 ≤ gN (Matrix.of (phi ε P u)) := Real.sqrt_nonneg _
    have h1 : hs (Matrix.of (phi ε P u) : Mat k r) ≤ R ^ 2 := by
      rw [hs_eq_gN]; exact pow_le_pow_left₀ h0 hu' 2
    have h2 : ((u : (Mat k r)ˣ) : Mat k r) = P * Matrix.of (phi ε P u) * P⁻¹ := (conj_back hP _).symm
    show hs ((u : (Mat k r)ˣ) : Mat k r) ≤ _
    rw [h2]
    have h3 : hs (P * Matrix.of (phi ε P u) * P⁻¹) ≤ hs P * hs (Matrix.of (phi ε P u) : Mat k r) * hs P⁻¹ :=
      (frobenius_mul_le _ _).trans (mul_le_mul_of_nonneg_right (frobenius_mul_le _ _) (hs_nonneg' _))
    have h4 : hs P * hs (Matrix.of (phi ε P u) : Mat k r) * hs P⁻¹ ≤ (hs P * hs P⁻¹) * R ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 hM0
      nlinarith
    have h5 : (hs P * hs P⁻¹) * R ^ 2 ≤ (M * R) ^ 2 := by
      rw [mul_pow]
      have : hs P * hs P⁻¹ ≤ M ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg R)
    linarith
  have hMR : 1 ≤ M * R := by nlinarith
  have e : R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) = R ^ (2 * (2 * r + k + 1) ^ 2) := by
    rw [← Real.rpow_natCast R (2 * (2 * r + k + 1) ^ 2)]; push_cast; rfl
  calc (c : ℝ≥0∞) * muG ε (phi ε P ⁻¹' {g : Mt k r | gN (Matrix.of g) ≤ R})
      ≤ (c : ℝ≥0∞) * ENNReal.ofReal (C * (M * R) ^ (2 * (2 * r + k + 1) ^ 2)) :=
        mul_le_mul_right ((measure_mono hsub).trans (hCV _ hMR)) _
    _ = ENNReal.ofReal (c * (C * M ^ (2 * (2 * r + k + 1) ^ 2)) * R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [e, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, mul_pow]
        congr 1; ring

theorem shell_int : ShellInt :=
  _root_.UpperTheory.Reformulated.B.LiftErrorLocal.shell_int

theorem gN_meas (k r : ℕ) : Measurable fun g : Mt k r => gN (Matrix.of g) := by
  unfold gN
  apply Measurable.sqrt
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have : Measurable fun g : Mt k r => g i j := (measurable_pi_apply j).comp (measurable_pi_apply i)
  exact Complex.continuous_normSq.measurable.comp this

theorem ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem gFromDiag' (hE : UJEmb) (hU : Unimodular) (hV : VolGrowth) (hF : HpkFacts) (hC : UHConj) :
    HaarGExists ∧ VolCrude := by
  constructor
  · intro k r
    obtain ⟨-, -, -, ε, -, P, hP, hH⟩ := hF k r
    exact ⟨_, haar_map hE hU hC hP hH⟩
  · intro k r μG hμ
    obtain ⟨-, -, -, ε, -, P, hP, hH⟩ := hF k r
    exact vol_crude hE hV hC hP hH μG hμ

end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem sharp_volume_of_exact : Formalism.FourierDecayAlt.B2.VolSharpFromExact := by
  intro hE k r μG hμ
  obtain ⟨C, -, hC⟩ := hE k r μG hμ
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hsub : {g : Mt k r | gN (Matrix.of g) ≤ R} ⊆
      {g | gN (Matrix.of g) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) + 4 * R ^ 2} := by
    intro g hg
    have h0 : 0 ≤ gN (Matrix.of g) := Real.sqrt_nonneg _
    have h1 : gN (Matrix.of g) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hg 2
    have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    show gN (Matrix.of g) ^ 2 ≤ _
    nlinarith [sq_nonneg R]
  refine (measure_mono hsub).trans ?_
  rw [hC R hR0]
  have e : R ^ (2 * ((k : ℝ) + r) * ((r : ℝ) + 1)) = R ^ (2 * (k + r) * (r + 1)) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [e, ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

theorem group_measure_from_diagonal : Formalism.FourierDecayAlt.B2.GFromDiag :=
  fun hE hU _ hV hF hC _ _ => HaarUniquenessConjugation.gFromDiag' hE hU hV hF hC

theorem norm_ball_volume_crude : Formalism.FourierDecayAlt.B2.VolCrude :=
  (HaarUniquenessConjugation.gFromDiag' uJEmb unimodular volGrowth hpkFacts uHConj).2

theorem norm_power_integrable_sharp_of_volume : Formalism.FourierDecayAlt.B2.GNIntSharpFromVol := by
  intro hS hL hV k r μG A hμ hA
  obtain ⟨C, hC⟩ := hV k r μG hμ
  refine hS (Mt k r) μG (fun g => gN (Matrix.of g)) C (2 * ((k : ℝ) + r) * ((r : ℝ) + 1)) A (HaarUniquenessConjugation.gN_meas k r) ?_
    (by positivity) hC ?_
  · filter_upwards [HaarUniquenessConjugation.ae_mem hμ] with g hg using hL k r _ hg
  · unfold AB at hA; linarith

theorem norm_power_integrable_crude : Formalism.FourierDecayAlt.B2.GNIntCrude := by
  intro k r μG A hμ hA
  obtain ⟨C, hC⟩ := norm_ball_volume_crude k r μG hμ
  refine HaarUniquenessConjugation.shell_int (Mt k r) μG (fun g => gN (Matrix.of g)) C _ A (HaarUniquenessConjugation.gN_meas k r) ?_ (by positivity) hC hA
  filter_upwards [HaarUniquenessConjugation.ae_mem hμ] with g hg using HaarUniquenessConjugation.gnLower k r _ hg

end Formalism.FourierDecayAlt.P
