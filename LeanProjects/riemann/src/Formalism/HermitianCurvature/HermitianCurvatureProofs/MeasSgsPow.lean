import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralAdjoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem one_le_gN (hNI : NormInv) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : 1 ≤ B.gN g :=
  ((hNI k r).2 g hg).2

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

def trivS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int

private lemma measurable_det_of_measurable_entries {α : Type*} [MeasurableSpace α] {n : ℕ} {F : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) : Measurable fun p => (F p).det := by
  simp_rw [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hF (σ i) i)

private lemma measurable_inv_apply_of_measurable_entries {α : Type*} [MeasurableSpace α] {n : ℕ} {F : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) : ∀ i j, Measurable fun p => (F p)⁻¹ i j := by
  intro i j
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine (measurable_det_of_measurable_entries hF).inv.mul (measurable_det_of_measurable_entries fun a c => ?_)
  rcases eq_or_ne a j with h | h <;> simp [Matrix.updateRow_apply, h, hF a c, measurable_const]

private lemma measurable_mul_apply_of_measurable_entries {α : Type*} [MeasurableSpace α] {n : ℕ} {F G : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) (hG : ∀ i j, Measurable fun p => G p i j) :
    ∀ i j, Measurable fun p => (F p * G p) i j := by
  intro i j
  simp_rw [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hF i l).mul (hG l j)

theorem meas_sgs_pow (γ : Mx k r) (b : ℝ) : Measurable fun p : B.SS k r => B.gN (B.sgs p γ) ^ (-b) := by
  have e : ∀ f : B.SS k r → Mt k r, Measurable f → ∀ i j, Measurable fun p => Matrix.of (f p) i j :=
    fun f hf i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)
  have h11 := e (fun p => p.1.1) (measurable_fst.comp measurable_fst)
  have h12 := e (fun p => p.1.2) (measurable_snd.comp measurable_fst)
  have h22 := e (fun p => p.2.2) (measurable_snd.comp measurable_snd)
  have h21 := e (fun p => p.2.1) (measurable_fst.comp measurable_snd)
  have hγ : ∀ i j, Measurable fun _ : B.SS k r => γ i j := fun _ _ => measurable_const
  have hS : ∀ i j, Measurable fun p => B.sgs p γ i j := by
    unfold B.sgs
    exact measurable_mul_apply_of_measurable_entries (measurable_mul_apply_of_measurable_entries (measurable_mul_apply_of_measurable_entries (measurable_mul_apply_of_measurable_entries (measurable_inv_apply_of_measurable_entries h11)
      (measurable_inv_apply_of_measurable_entries h12)) hγ) h22) h21
  unfold B.gN
  refine Measurable.pow_const (Measurable.sqrt ?_) _
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.measurable.comp (hS i j)

def fZ (b : ℝ) (g : B.Mat k r) : ℂ →L[ℂ] ℂ := ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)

theorem fZ_inCC (hNI : NormInv) (b : ℝ) : B.InCC b 0 (fZ (k := k) (r := r) b) := by
  have hge : ∀ g ∈ B.GV k r, 1 ≤ B.gN g := fun g hg => ((hNI k r).2 g hg).2
  have hcont : Continuous fun g : B.Mat k r => B.gN g := by
    unfold B.gN
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)
  refine ⟨1, ?_, ?_⟩
  · intro g₀ hg₀
    refine ⟨{g | 1 / 2 < B.gN g}, fZ b, isOpen_lt continuous_const hcont,
      show (1 / 2 : ℝ) < B.gN g₀ by linarith [hge g₀ hg₀], ?_, fun g _ _ => rfl⟩
    have hc : ContinuousOn (fun g : B.Mat k r => fZ (k := k) (r := r) b g) {g | 1 / 2 < B.gN g} := by
      have h0 : ContinuousOn (fun g : B.Mat k r => B.gN g ^ (-b)) {g | 1 / 2 < B.gN g} :=
        hcont.continuousOn.rpow_const fun g hg =>
          Or.inl (ne_of_gt (by have : (1 / 2 : ℝ) < B.gN g := hg; linarith))
      exact (Complex.continuous_ofReal.comp_continuousOn h0).smul continuousOn_const
    exact (contDiffOn_zero.2 hc).of_le (by norm_num)
  · intro u v _ _ hlen g hg
    obtain rfl : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hpos : 0 < B.gN g := lt_of_lt_of_le one_pos (hge g hg)
    simp only [B.dLR, B.Rw, List.foldr_nil, fZ, norm_smul, Complex.norm_real, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le (-b))]
    rw [Real.rpow_neg hpos.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos b).ne']

theorem orb_gN (hJC : JF.JConv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (hNI : NormInv) {b : ℝ}
    (hThr : JF.TransportedAlt k r b 0) {γ : Mx k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    Integrable (fun p => B.gN (B.sgs p γ) ^ (-b)) D.μSS := by
  obtain ⟨-, h2⟩ := hJC k r ℂ ℂ (trivS D) b (fZ b) hThr (fZ_inCC (k := k) (r := r) hNI b)
  obtain ⟨bd, hbd, hle⟩ := h2 {γ} isCompact_singleton (Set.singleton_subset_iff.2 hγ)
  refine hbd.mono' (meas_sgs_pow γ b).aestronglyMeasurable ?_
  filter_upwards [hle γ rfl] with p hp

  have e : B.rho (trivS D) p (fZ b) γ = fZ b (B.sgs p γ) := by
    ext
    simp [B.rho, trivS]
  have e2 : ‖fZ (k := k) (r := r) b (B.sgs p γ)‖ = ‖B.gN (B.sgs p γ) ^ (-b)‖ := by
    simp [fZ, norm_smul, Complex.norm_real]
  rw [← e2, ← e]
  exact hp

end Formalism.FourierDecayAlt.P.S3dx6
