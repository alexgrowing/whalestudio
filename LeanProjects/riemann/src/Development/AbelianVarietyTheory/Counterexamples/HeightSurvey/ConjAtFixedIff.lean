import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.SmoothAutCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

theorem conj_fixed_iff (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    -(H⁻¹ * Zᴴ * H) = Z ↔ Zᴴ * H + H * Z = 0 := by
  constructor
  · intro h
    have : H * Z = -(Zᴴ * H) := by
      conv_lhs => rw [← h]
      rw [mul_neg, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hu, one_mul]
    rw [this, add_neg_cancel]
  · intro h
    have : Zᴴ * H = -(H * Z) := eq_neg_of_add_eq_zero_left h
    rw [mul_assoc, this, mul_neg, neg_neg, ← mul_assoc, nonsing_inv_mul _ hu, one_mul]

theorem conjT_conj_mul (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (-(H⁻¹ * Zᴴ * H))ᴴ * H = -(H * Z) := by
  rw [conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    neg_mul, mul_assoc, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem mul_conj (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) : H * (-(H⁻¹ * Zᴴ * H)) = -(Zᴴ * H) := by
  rw [mul_neg, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hu, one_mul]

theorem re_mem (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H)))ᴴ * H + H * ((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H))) = 0 := by
  rw [conjTranspose_smul, conjTranspose_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, conjT_conj_mul hH hu,
    mul_conj hu]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem im_mem (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / (2 * Complex.I)) • (Z - -(H⁻¹ * Zᴴ * H)))ᴴ * H + H * ((1 / (2 * Complex.I)) • (Z - -(H⁻¹ * Zᴴ * H))) = 0 := by
  rw [conjTranspose_smul, conjTranspose_sub, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, conjT_conj_mul hH hu,
    mul_conj hu]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [this, neg_smul, sub_neg_eq_add, sub_neg_eq_add, add_comm (H * Z), neg_add_cancel]

theorem exp_mem_UH (hu : IsUnit H.det) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : (t • X)ᴴ = H * (-(t • X)) * H⁻¹ := by
    have h1 : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(H * X) * H⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

end Lin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem gram_det_ne : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0 := by
    intro y
    rw [← V.frame.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h0 i
    simp only [mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    calc _ = (starRingEnd _) (V.frame.repr y i) * ∑ j, V.hT (V.frame i) (V.frame j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have := V.nondeg.2 _ hx
  exact hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))

theorem gramAt_unit (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero _).2 (gram_det_ne V)

theorem gramAt_herm (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [conjTranspose_apply, gramAt, map_apply, HSpace.gram]
  rw [← h1]
  exact (NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem conjAt_fixed_iff (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ Z = Z ↔ Z ∈ lieAt V τ := conj_fixed_iff (gramAt_unit V τ) Z

theorem parts_mem (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / 2 : ℂ) • (Z + conjAt V τ Z) ∈ lieAt V τ ∧ (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) ∈ lieAt V τ :=
  ⟨re_mem (gramAt_herm V τ) (gramAt_unit V τ) Z, im_mem (gramAt_herm V τ) (gramAt_unit V τ) Z⟩

theorem parts_sum (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / 2 : ℂ) • (Z + conjAt V τ Z) + Complex.I • ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) = Z := by
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, this, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  simp

theorem RderC_eq (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    RderC θ V τ X φ = Rder θ V τ X φ := by
  unfold RderC
  rw [(conjAt_fixed_iff V τ X).2 hX, sub_self, smul_zero, ← two_smul ℂ X, smul_smul]
  have : Rder θ V τ 0 φ = 0 := by
    funext g
    simp [Rder, oneP]
  rw [this]
  simp

theorem oneP_spec {X : ThetaX D} (T : ThetaTied D X) (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau)
    {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (t : ℝ) :
    IsAtTau θ V τ (NormedSpace.exp (t • Y)) (oneP θ V τ Y t) := by
  have h := (T.actR.2 θ hθ V τ _ (exp_mem_UH (gramAt_unit V τ) hY t)).1
  unfold oneP atTau
  rw [dif_pos h]
  exact h.choose_spec

def reSig (s : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D := { V with sig := s }

theorem isAutFunSm_reSig (s : (D.host.E →+* ℂ) → ℕ × ℕ) (φ : GA D V → ℂ) :
    IsAutFunSm θ (reSig V s) φ ↔ IsAutFunSm θ V φ :=
  ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
   fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

end GlobalTheory.SmoothAutCheck

end
