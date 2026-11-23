import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.FrameDual

section Det

variable {A : Type} [CommRing A]

end Det

section Ideals

variable {E : Type} [Field E] [NumberField E]

def Stab (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) : Prop := ∀ x ∈ I, σ x ∈ I

theorem stab_one (σ : E →+* E) : Stab σ 1 := by
  intro x hx
  obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact (FractionalIdeal.mem_one_iff _).2 ⟨RingOfIntegers.mapRingHom σ d, rfl⟩

theorem Stab.mul {σ : E →+* E} {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (hJ : Stab σ J) :
    Stab σ (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)
  · rw [map_add]; exact Submodule.add_mem (I * J).coeToSubmodule ha hb

theorem Stab.pow {σ : E →+* E} {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (j : ℕ) :
    Stab σ (I ^ j) := by
  induction j with
  | zero => simpa using stab_one σ
  | succ j ih => rw [pow_succ]; exact ih.mul hI

theorem Stab.inv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I)
    (h0 : I ≠ 0) : Stab σ I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have := stab_one σ _ (hx _ (hI y hy))
  rwa [map_mul, hσ] at this

theorem diff_ne_zero : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem dInv_ne_zero (j : ℕ) : dInv E j ≠ 0 := pow_ne_zero _ (inv_ne_zero diff_ne_zero)

theorem stab_dInv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (j : ℕ) : Stab σ (dInv E j) := by
  refine Stab.pow ?_ j
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  intro x hx
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h10] at hx ⊢
  intro a ha
  have h1 := hx _ (stab_one σ a ha)
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have h2 : Algebra.traceForm ℚ E (σ x) a = Algebra.traceForm ℚ E x (σ a) := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv e (x * σ a)]
    congr 1
    change _ = σ (x * σ a)
    rw [map_mul, hσ]
  rwa [h2]

end Ideals

section Frame

variable {E : Type} [Field E] [NumberField E]

theorem frameDualTupleIdeals_castAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.castAdd r b.castSucc) = dInv E (r - b) := by
  simp [id1]

theorem frameDualTupleIdeals_natAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.natAdd (r + 1) b) = (dInv E (r - b))⁻¹ := by
  simp [id1]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem natAbs_discr_sq (h2 : Module.finrank F E = 2) [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] :
    (discr E).natAbs = (discr F).natAbs ^ 2 := by
  have h0 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact not_dvd_differentIdeal_iff.2 (inferInstance : Algebra.IsUnramifiedAt (𝓞 F) P)
      (Ideal.dvd_iff_le.2 hle)
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rwa [h0, Ideal.absNorm_top, one_mul, h2] at h1

theorem absNorm_dInv (j : ℕ) :
    ((FractionalIdeal.absNorm (dInv E j) : ℚ) : ℝ) = |(discr E : ℝ)|⁻¹ ^ j := by
  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E (𝓞 E)]
  simp

end Frame

end GlobalTheory.SnMass.FrameDual
