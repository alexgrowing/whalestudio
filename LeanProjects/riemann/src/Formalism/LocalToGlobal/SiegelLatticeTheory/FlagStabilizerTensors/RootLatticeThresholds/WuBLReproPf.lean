import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc

noncomputable section

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal InnerProductSpace
open Matrix

namespace Formalism.L2.SG.Pf.WuBL

variable {k r : ℕ}

def conjH (a b a' b' : Formalism.FourierDecayAlt.B.Mat k r) (hab : a' * a = 1) (hbb : b * b' = 1) (hab' : a * a' = 1)
    (hbb' : b' * b = 1) : Mt k r ≃ₜ Mt k r where
  toFun g := Matrix.of.symm (a * Matrix.of g * b)
  invFun g := Matrix.of.symm (a' * Matrix.of g * b')
  left_inv g := by
    show Matrix.of.symm (a' * (a * Matrix.of g * b) * b') = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hab, Matrix.one_mul, Matrix.mul_assoc, hbb, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of.symm (a * (a' * Matrix.of g * b') * b) = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hab', Matrix.one_mul, Matrix.mul_assoc, hbb', Matrix.mul_one]; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    fun_prop
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    fun_prop

theorem meas_rmul (a : Formalism.FourierDecayAlt.B.Mat k r) : Measurable (Formalism.FourierDecayAlt.B.rmulF a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.FourierDecayAlt.B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private theorem hpk_sq_lemma {k r : ℕ} : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
    · intro l _ hl
      have h0 : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
      rw [h0, zero_mul]
    · simp
  · have hlt : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hlt⟩]
    · simp only [Hpk]
      split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
    · intro l _ hl
      have h0 : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (try simp only [Fin.ext_iff, ne_eq, Fin.val_mk, and_true, true_and, not_true_eq_false, not_false_eq_true] at *) <;>
        first | omega | (norm_num; done) | (exfalso; omega)
      rw [h0, zero_mul]
    · simp

theorem reproduction_translation : ReproTr := by
  intro k r μG hμ H _ _ σ hσ hiso Vp _ _ W w y hy hrep x hx
  have hmulU : ∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r) := by
    intro a ha b hb
    have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
    have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha', hb']
  obtain ⟨yi, hyi⟩ : ∃ yi : Formalism.FourierDecayAlt.B.Mat k r, yi = Hpk k r * yᴴ * Hpk k r := ⟨_, rfl⟩
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hyiy : yi * y = 1 := by
    rw [hyi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc yᴴ, hy', hpk_sq_lemma]
  have hyyi : y * yi = 1 := mul_eq_one_comm.1 hyiy
  have hyiU : yi ∈ UH (Hpk k r) := by
    show yiᴴ * Hpk k r * yi = Hpk k r
    calc yiᴴ * Hpk k r * yi = yiᴴ * (yᴴ * Hpk k r * y) * yi := by rw [hy']
      _ = (y * yi)ᴴ * Hpk k r * (y * yi) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hyyi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcU : ∀ g ∈ UH (Hpk k r), yi * g * y ∈ UH (Hpk k r) := fun g hg =>
    hmulU _ (hmulU _ hyiU _ hg) _ hy
  have hinner : ∀ g ∈ UH (Hpk k r), ∀ u v : H, ⟪σ g u, σ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro g hg u v
    let L : H →ₗᵢ[ℂ] H := ⟨(σ g : H →ₗ[ℂ] H), fun z => hiso g hg z⟩
    exact L.inner_map_map u v
  have hinnerc : ∀ g ∈ UH (Hpk k r), ⟪σ y w, σ g (σ y w)⟫_ℂ = ⟪w, σ (yi * g * y) w⟫_ℂ := by
    intro g hg
    have e1 : g * y = y * (yi * g * y) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyyi, Matrix.one_mul]
    have h1 : σ g (σ y w) = σ y (σ (yi * g * y) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hσ.2 g hg y hy, e1, hσ.2 y hy _ (hcU g hg),
        ContinuousLinearMap.comp_apply]
    rw [h1, hinner y hy]
  have hmL : Measurable (lmulM (k := k) (r := r) yi) := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Mt k r ≃ₜ Mt k r, Φ = conjH yi y y yi hyyi hyyi hyiy hyiy := ⟨_, rfl⟩
  have hΦg : ∀ g : Mt k r, Matrix.of (Φ g) = yi * Matrix.of g * y := by
    intro g
    rw [hΦdef] <;> rfl
  have hΦ : MeasurePreserving Φ μG μG := by
    rw [hΦdef]
    exact (⟨meas_rmul y, hμ.right y hy⟩ : MeasurePreserving (Formalism.FourierDecayAlt.B.rmulF y) μG μG).comp
      ⟨hmL, hμ.left yi hyiU⟩
  have hae : ∀ᵐ z ∂μG, Matrix.of z ∈ UH (Hpk k r) := by
    have h0 : μG (UH (Hpk k r))ᶜ = 0 := hμ.conc
    filter_upwards [compl_mem_ae_iff.2 h0] with z hz
    by_contra hc
    exact hz hc
  have hfdeg : fdegH μG σ (σ y w) = fdegH μG σ w := by
    unfold fdegH
    rw [hiso y hy w]
    congr 1
    have hint : (fun z : Mt k r => ‖⟪σ y w, σ (Matrix.of z) (σ y w)⟫_ℂ‖ ^ 2) =ᵐ[μG]
        (fun z => ‖⟪w, σ (Matrix.of (Φ z)) w⟫_ℂ‖ ^ 2) := by
      filter_upwards [hae] with z hz
      rw [hinnerc _ hz, hΦg]
    rw [integral_congr_ae hint]
    exact hΦ.integral_comp Φ.measurableEmbedding (fun h => ‖⟪w, σ (Matrix.of h) w⟫_ℂ‖ ^ 2)
  have heF : ∀ g : Mt k r, Matrix.of g ∈ UH (Hpk k r) →
      eFun μG σ (σ y w) (Matrix.of g) = eFun μG σ w (Matrix.of (Φ g)) := by
    intro g hg
    unfold eFun
    rw [hfdeg, hinnerc _ hg, hΦg]
  have e2 : ∀ g : Mt k r, x * Matrix.of g * y = x * y * Matrix.of (Φ g) := by
    intro g
    rw [hΦg]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y yi, hyyi, Matrix.one_mul]
  have hpt : (fun g : Mt k r => eFun μG σ (σ y w) (Matrix.of g) • W (x * Matrix.of g * y)) =ᵐ[μG]
      (fun g => eFun μG σ w (Matrix.of (Φ g)) • W (x * y * Matrix.of (Φ g))) := by
    filter_upwards [hae] with g hg
    rw [heF g hg, e2 g]
  obtain ⟨hI, hR⟩ := hrep (x * y) (hmulU _ hx _ hy)
  refine ⟨?_, ?_⟩
  · have h2 : Integrable (fun g => eFun μG σ w (Matrix.of (Φ g)) • W (x * y * Matrix.of (Φ g))) μG :=
      (hΦ.integrable_comp_emb Φ.measurableEmbedding).2 hI
    exact h2.congr hpt.symm
  · unfold rconv at hR ⊢
    calc ∫ g, eFun μG σ (σ y w) (Matrix.of g) • W (x * Matrix.of g * y) ∂μG
        = ∫ g, eFun μG σ w (Matrix.of (Φ g)) • W (x * y * Matrix.of (Φ g)) ∂μG := integral_congr_ae hpt
      _ = ∫ h, eFun μG σ w (Matrix.of h) • W (x * y * Matrix.of h) ∂μG :=
          hΦ.integral_comp Φ.measurableEmbedding (fun h => eFun μG σ w (Matrix.of h) • W (x * y * Matrix.of h))
      _ = W (x * y) := hR

end Formalism.L2.SG.Pf.WuBL
