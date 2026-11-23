import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNormReduce

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hE_sub_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b y : Fin M → E) (c : E) :
    hE σ J (a - c • b) y = hE σ J a y - σ c * hE σ J b y := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_sub_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y a b : Fin M → E) (c : E) :
    hE σ J y (a - c • b) = hE σ J y a - c * hE σ J y b := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_swap' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (x y : Fin M → E) : hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

end Alg

theorem sigma_sigma' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem reduce : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x z : Fin M → E, hE σ J x x ≠ 0 → IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) → hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0 := by
  intro F E _ _ _ _ _ σ hCM K _ _ M J hJ x z hx hN
  have hσ := sigma_sigma' σ hCM
  set a := hE σ J x x with ha
  set c := hE σ J x z / a with hc
  set q := hE σ J (z - c • x) (z - c • x) with hq
  have hsa : σ a = a := (hE_swap' σ hσ J hJ x x).symm
  have hzx : hE σ J z x = σ (hE σ J x z) := hE_swap' σ hσ J hJ x z
  have hsc : σ c = hE σ J z x / a := by rw [hc, map_div₀, hsa, hzx]

  have hqa : q * a = gram2E σ J x z := by
    rw [hq, hE_sub_smul_left, hE_sub_smul_right, hE_sub_smul_right, hsc, hc, gram2E]
    field_simp
    ring

  obtain ⟨s, hs, hss⟩ := hN
  have hinj : Function.Injective (inclR (F := F) (E := E) K) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hG : gram2E σ J x z ≠ 0 := by
    intro h0
    rw [h0, map_zero, neg_zero] at hss
    have hu : IsUnit (0 : K ⊗[F] E) := by
      rw [← hss]; exact hs.mul (hs.map (sigR K σ))
    have h01 : (0 : K ⊗[F] E) = 1 := isUnit_zero_iff.mp hu
    have : inclR (F := F) K (0 : E) = inclR (F := F) K 1 := by rw [map_zero, map_one, h01]
    exact zero_ne_one (hinj this)
  have hq0 : q ≠ 0 := by
    intro h0; apply hG; rw [← hqa, h0, zero_mul]
  refine ⟨hq0, ?_⟩

  set v : K ⊗[F] E := ↑(hs.unit⁻¹) with hv
  have h1 : v * s = 1 := by rw [hv]; exact hs.val_inv_mul
  have h2 : sigR K σ v * sigR K σ s = 1 := by rw [← map_mul, h1, map_one]
  refine ⟨inclR K a * v, ?_⟩
  have hw : IsUnit (s * sigR K σ s) := hs.mul (hs.map (sigR K σ))
  apply hw.mul_left_eq_zero.mp
  have e1 : inclR K a * v * sigR K σ (inclR K a * v) * (s * sigR K σ s) = inclR K (a * a) := by
    rw [map_mul, sigR_inclR', hsa]
    calc inclR K a * v * (inclR K a * sigR K σ v) * (s * sigR K σ s)
        = inclR K a * inclR K a * (v * s) * (sigR K σ v * sigR K σ s) := by ring
      _ = inclR K (a * a) := by rw [h1, h2, map_mul]; ring
  have e2 : inclR K (a / q) * (s * sigR K σ s) = - inclR K (a * a) := by
    rw [hss, mul_neg, ← map_mul, ← hqa]
    congr 2
    field_simp
  rw [add_mul, e1, e2, add_neg_cancel]

end GlobalTheory.PlaneNormReduce
