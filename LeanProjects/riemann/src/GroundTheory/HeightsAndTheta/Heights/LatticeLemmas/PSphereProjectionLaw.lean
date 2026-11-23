import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereProjectionLaw

variable {n : ℕ}

theorem ofReal_norm_sq (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * star x := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ofReal_sum_norm_sq (v : Fin n → ℂ) :
    ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) = ∑ j, v j * star (v j) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ ↦ ofReal_norm_sq (v j)

theorem coordAlong_smul (p w : Fin n → ℂ) (c : ℂ) :
    coordAlong p (c • w) = c * coordAlong p w := by
  simp [coordAlong, Finset.mul_sum, mul_assoc]

theorem coordAlong_sub (p z w : Fin n → ℂ) :
    coordAlong p (z - w) = coordAlong p z - coordAlong p w := by
  simp [coordAlong, sub_mul, Finset.sum_sub_distrib]

theorem coordAlong_self {p : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) : coordAlong p p = 1 := by
  rw [coordAlong, ← ofReal_sum_norm_sq, hp, Complex.ofReal_one]

theorem std_norm (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem sum_norm_sq_smul (c : ℂ) (w : Fin n → ℂ) :
    ∑ j, ‖(c • w) j‖ ^ 2 = ‖c‖ ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]

theorem sum_norm_sq_sub {p z : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hz : ∑ j, ‖z j‖ ^ 2 = 1) :
    ∑ j, ‖(z - coordAlong p z • p) j‖ ^ 2 = 1 - ‖coordAlong p z‖ ^ 2 := by
  apply Complex.ofReal_injective
  set a := coordAlong p z with ha
  have hzp : ∑ j, p j * star (z j) = star a := by
    simp [ha, coordAlong, star_sum, mul_comm]
  have hpp : ∑ j, p j * star (p j) = 1 := by rw [← ofReal_sum_norm_sq, hp, Complex.ofReal_one]
  have hzz : ∑ j, z j * star (z j) = 1 := by rw [← ofReal_sum_norm_sq, hz, Complex.ofReal_one]
  have key : ∀ j, (z - a • p) j * star ((z - a • p) j) =
      z j * star (z j) - star a * (z j * star (p j)) - a * (p j * star (z j)) +
        a * star a * (p j * star (p j)) := by
    intro j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
    ring
  rw [ofReal_sum_norm_sq, Finset.sum_congr rfl fun j _ ↦ key j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hzp, hpp, hzz, ← coordAlong, ← ha, Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_norm_sq]
  ring

theorem exists_unitary_first {m : ℕ} (p : Fin (m + 1) → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    ∃ U : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ),
      (∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2) ∧ ∀ v, U v 0 = coordAlong p v := by
  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (Set.mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  have hUapp : ∀ v, Ulin v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v ↦ rfl
  refine ⟨Ulin.toLinearMap, fun v ↦ ?_, fun v ↦ ?_⟩
  · have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
    simpa [hUapp] using h2
  · rw [LinearEquiv.coe_coe, hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply, coordAlong]

theorem span_singleton_ne_top {N : ℕ} (hN : 2 ≤ N) (p : Fin N → ℂ) :
    Submodule.span ℂ {p} ≠ ⊤ := by
  intro h
  have h1 := finrank_span_le_card (R := ℂ) ({p} : Set (Fin N → ℂ))
  rw [h, finrank_top, Module.finrank_fin_fun] at h1
  simp at h1
  omega

end SphereProjectionLaw

open SphereProjectionLaw in

theorem SphereProjectionLaw.proof (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement)
    (h3 : SphereLawFirstCoord.Statement) (h4 : SpherePhase.Statement) :
    SphereProjectionLaw.Statement := by
  intro N p hp
  refine ⟨fun hN ↦ ?_, fun hN ↦ ⟨?_, h4 N p hp hN, ?_⟩⟩
  ·
    subst hN
    filter_upwards [(h1 1 le_rfl).2.1] with z hz
    simp only [Fin.sum_univ_one] at hz hp
    have hz1 : ‖z 0‖ = 1 := by nlinarith [norm_nonneg (z 0)]
    have hp1 : ‖p 0‖ = 1 := by nlinarith [norm_nonneg (p 0)]
    simp [coordAlong, hz1, hp1]
  ·
    have hnull := measure_eq_zero_iff_ae_notMem.mp
      ((h1 N (by omega)).2.2 _ (span_singleton_ne_top hN p))
    filter_upwards [(h1 N (by omega)).2.1, hnull] with z hz hzS
    set a := coordAlong p z with ha
    set w := z - a • p with hw
    have hw0 : w ≠ 0 := by
      intro h
      apply hzS
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨a, (sub_eq_zero.mp h).symm⟩
    have hsq : ∑ j, ‖w j‖ ^ 2 = 1 - ‖a‖ ^ 2 := sum_norm_sq_sub hp hz
    have hpos : 0 < ∑ j, ‖w j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
      calc (0 : ℝ) < ‖w j‖ ^ 2 := by positivity
        _ ≤ ∑ j, ‖w j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j ↦ ‖w j‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    set s := √(1 - ‖a‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (hsq ▸ hpos)
    have hss : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (hsq ▸ hpos.le)
    have hdir : orthoDir p z = ((s : ℂ))⁻¹ • w := by
      rw [orthoDir, std_norm, ← ha, ← hw, hsq]
    have hwp : coordAlong p w = 0 := by
      rw [hw, coordAlong_sub, coordAlong_smul, coordAlong_self hp, mul_one, sub_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdir, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs0.ne'), one_smul, hw,
        add_sub_cancel]
    · rw [hdir, coordAlong_smul, hwp, mul_zero]
    · rw [hdir, std_norm, sum_norm_sq_smul, hsq, ← hss, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs0.le, inv_pow, inv_mul_cancel₀ (pow_pos hs0 2).ne', Real.sqrt_one]
  ·
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    obtain ⟨U, hU, hU0⟩ := exists_unitary_first p hp
    have hf : (fun z ↦ ‖coordAlong p z‖ ^ 2) =
        (fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2) ∘ U := by
      funext z
      simp [hU0]
    have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
    have hgm : Measurable fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2 :=
      ((continuous_apply _).norm.pow 2).measurable
    rw [hf, ← Measure.map_map hgm hUm, h2 _ U hU, h3 _ hN]

end

end GroundTheory.Heights₂.Heights
