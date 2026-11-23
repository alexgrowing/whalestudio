import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem rexp_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  intro E _ _ _ x ha
  refine ⟨?_, (CG.isUnitary_mk _).symm⟩
  have hc : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ :=
    Classical.epsilon_spec (p := fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ)
      (by rw [zc_eq_scL]; exact Central.lie_scalar x.2 (1 : Cinf E))
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hpos : (0 : ℝ) < x.1 * Module.finrank ℚ E := by positivity
  have hz := (zc_comm_mem_eigen E x.1).2.2
  rw [rexp, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h0
    have hne : (x.1 * (Module.finrank ℚ E : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    obtain ⟨χ, h1, -, h2, -⟩ := exists_abs_cpow E (-cex x / (x.1 * (Module.finrank ℚ E : ℂ)))
    have hre : (-cex x / (x.1 * (Module.finrank ℚ E : ℂ))).re = 0 := by
      rw [← Nat.cast_mul, Complex.div_natCast_re, Complex.neg_re, h0]; simp
    have hχ : χ.IsUnitary := fun y => by
      rw [h2, hre, nu, Model.eq_one_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E 0)]
      exact isUnitary_one y
    have hn : IsNormalised (x.2.twist χ) := by
      rintro _ ⟨φ, hφ, rfl⟩ t g
      have h3 : zc E x.1 (mulChi x.1 χ φ) = (0 : ℂ) • mulChi x.1 χ φ := by
        rw [h1, hc φ hφ, mul_div_cancel₀ _ hne, ← add_smul, add_neg_cancel, map_smul]
      simpa using (hz _ 0).1 h3 t g
    obtain ⟨ω, hω⟩ := Central.exists_hasCentral E x.1 x.2
    have h4 := ((hω.twist χ).isUnitary_iff.1 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)).mul
      (isUnitary_pow hχ x.1).inv
    rw [mul_inv_cancel_right] at h4
    exact hω.isUnitary_iff.2 h4
  · intro hu
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.2.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
    have h1 := congrArg norm ((hz φ _).1 (hc φ hφ) 1 g)
    rw [splitCentre_eq_scalar, hu.norm_eq hφ, norm_mul, Complex.norm_exp] at h1
    have h2 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h1.symm
    simpa using h2

end GlobalTheory.ResW
