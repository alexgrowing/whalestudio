import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_form_of_mem_stdAt (a : E) (η : Sp E n →ₗ[E] E) (h : ∀ i, IntAt P (a * η (Pi.single i 1))) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : IntAt P (a * η v) := by
  rw [GlobalTheory.TopInv.form_apply η v, Finset.mul_sum]
  refine GlobalTheory.TopStep.intAt_sum _ fun j _ => ?_
  rw [mul_left_comm]
  exact (mem_stdAt.1 hv j).mul (h j)

theorem intAt_form_comp_iff (a : E) (κ : GLint E n P) (η : Sp E n →ₗ[E] E) :
    (∀ i, IntAt P (a * (η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔ ∀ i, IntAt P (a * η (Pi.single i 1)) := by
  refine ⟨fun h i => ?_, fun h i => intAt_form_of_mem_stdAt a η h (glint_mem κ (single_mem_stdAt i))⟩
  have h1 := intAt_form_of_mem_stdAt a _ h (glint_mem κ⁻¹ (single_mem_stdAt i))
  have e : κ.1 ((κ⁻¹).1 (Pi.single i 1)) = Pi.single i 1 := LinearEquiv.apply_symm_apply κ.1 _
  have e' : (η ∘ₗ κ.1.toLinearMap) ((κ⁻¹).1 (Pi.single i 1)) = η (Pi.single i 1) := congrArg η e
  rwa [e'] at h1

end SlopeTestRemainingChoices

theorem psi_add_int {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) {k : ℕ}
    (hk : k ≤ c.D P) {x z : X.E} (hx : IntAt P.1 ((qOf P.1 : X.E) ^ k * x)) (hz : IntAt P.1 (z - x)) :
    c.psi P ((epsSg : X.E) * z) = c.psi P ((epsSg : X.E) * x) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
  have hq := fun m => intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P.1) (qOf P.1)) m
  have hd := he.mul hz
  have h1 : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * ((epsSg : X.E) * x)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have := (hq d).mul (he.mul hx)
    convert this using 1
    rw [hd, pow_add]
    ring
  have := hc.psi_add P _ _ h1 ((hq _).mul hd)
  rw [hc.psi_int P _ hd, mul_one] at this
  rw [← this]
  congr 1
  ring

theorem ftY_comp_glint : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (P : rowSG Pr sel mu), (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ {n : ℕ} (κ : GLint X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) (y' y'' : Sp X.E n), (P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → (P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) → (P.1 ∈ Pr.vGs → κ.1 y'' - y' ∈ stdAt X.E n P.1) → (P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 y'' - y') ∈ stdAt X.E n P.1) → ftY sel mu cst P (η ∘ₗ κ.1.toLinearMap) y'' = ftY sel mu cst P η y' := by
  intro X Pr sel S mu cst hc P hD n κ η y' y'' hy1 hy2 hk1 hk2
  have hq := qOf_ne_zero (P := P.1)
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP, if_pos hP]
    have hi := intAt_form_comp_iff 1 κ η
    simp only [one_mul] at hi
    by_cases h : ∀ i, IntAt P.1 (η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      have h' : ∀ i, IntAt P.1 (1 * η (Pi.single i 1)) := fun i => by rw [one_mul]; exact h i
      refine psi_add_int hc P (hc.D_pos P) ?_ ?_
      · have := intAt_form_of_mem_stdAt 1 η h' (v := (qOf P.1 : X.E) • y') (mem_stdAt.2 (hy1 hP))
        rwa [one_mul, map_smul, smul_eq_mul, ← pow_one (qOf P.1 : X.E)] at this
      · have := intAt_form_of_mem_stdAt 1 η h' (hk1 hP)
        rwa [one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]
  · rw [if_neg hP, if_neg hP]
    have hi := intAt_form_comp_iff ((qOf P.1 : X.E) ^ cst.M) κ η
    by_cases h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      refine congrArg _ (psi_add_int hc P (hD hP) ?_ ?_)
      · have := intAt_form_of_mem_stdAt _ η h (v := (qOf P.1 : X.E) ^ cst.M • y') (mem_stdAt.2 (hy2 hP))
        rwa [map_smul, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul] at this
      · have := intAt_form_of_mem_stdAt _ η h (hk2 hP)
        rwa [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]

end GlobalTheory.TopLaw
