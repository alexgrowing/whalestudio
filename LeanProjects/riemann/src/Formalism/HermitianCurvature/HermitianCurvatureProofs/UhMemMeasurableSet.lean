import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbConvDDOfDecDD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

private theorem conj_mem_lemma {ε : Fin (2 * r + k + 1) → Bool} {P a : Mx k r}
    (h1 : P * P⁻¹ = 1) (hPJ : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ PI.UpqRep.UJset ε := by
  have ha' : aᴴ * PI.UpqRep.Hpk k r * a = PI.UpqRep.Hpk k r := ha
  have hc : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (P * a * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * a * P⁻¹) = PI.UpqRep.Jm ε
  calc (P * a * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * a) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹ := by rw [hPJ, ha']
      _ = (P⁻¹)ᴴ * Pᴴ * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hc, h1, Matrix.one_mul, Matrix.mul_one]

theorem sigma_mul' {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {a b : Mx k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hds
  obtain ⟨-, -, ⟨⟨-, hmulU⟩, -, -⟩, -⟩ := hDS
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have key : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have hprod : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
    rw [show P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ by
      simp only [Matrix.mul_assoc], h2, Matrix.mul_one, Matrix.mul_assoc P a b]
  have hmul := hmulU _ (conj_mem_lemma h1 hPJ ha) _ (conj_mem_lemma h1 hPJ hb)
  simp only [hprod, key] at hmul
  exact hmul

theorem dd_stable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∀ x ∈ DDsp σ w0, σ g x ∈ DDsp σ w0 := by
  intro x hx
  have hmm : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']
  unfold DDsp at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, hh, rfl⟩ := hy
    have e : σ g (σ h w0) = σ (g * h) w0 := by
      rw [sigma_mul' hds hg hh, ContinuousLinearMap.comp_apply]
    rw [e]
    exact Submodule.subset_span ⟨g * h, hmm g hg h hh, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

theorem l_of_be {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {σ : Mx k r → (H →L[ℂ] H)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {l : H → Wp} {x v : H}
    (hbe : be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)) (hlv : l v ≠ 0) :
    l x = ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ • (be z c π σ μW μN x v) (l v) := by
  have hn : ((‖l v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h0 : ‖l v‖ ≠ 0 := norm_ne_zero_iff.mpr hlv
    exact_mod_cast pow_ne_zero 2 h0
  have key : (be z c π σ μW μN x v) (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l x := by
    rw [hbe]
    simp [inner_self_eq_norm_sq_to_K]
  rw [key, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem coef_ext {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (v x : H) :
    ∃ e : Mx k r → ℂ, Continuous e ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e g = ⟪v, σ g x⟫_ℂ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hds
  obtain ⟨-, -, ⟨-, -, hcontU⟩, -⟩ := hDS
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have key : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have hφ : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hcont : ContinuousOn (fun g : Mx k r => σ g x) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have hc := (hcontU x).comp hφ.continuousOn (fun _ hg => conj_mem_lemma h1 hPJ hg)
    refine hc.congr fun g _ => ?_
    simp only [Function.comp_apply, key]
  have hid : Continuous fun g : Mx k r => g := continuous_id
  have hcl : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    show IsClosed {g : Mx k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
    exact isClosed_eq ((hid.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hid)
      continuous_const
  let f : C(Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ℂ) :=
    ⟨fun g => ⟪v, σ g x⟫_ℂ, (continuousOn_const.inner hcont).restrict⟩
  haveI : NormalSpace (Mx k r) :=
    inferInstanceAs (NormalSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hcl f
  exact ⟨⇑G, G.continuous, fun g hg => DFunLike.congr_fun hG ⟨g, hg⟩⟩

theorem uh_mem_measurableSet :
    MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have h0 : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r) := continuous_id
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x :=
    (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
  exact (isClosed_eq hc continuous_const).measurableSet

end Formalism.FourierDecayAlt.P.S3dx4
