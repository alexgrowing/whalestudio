import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRepEndomorphismScalarSchurStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigenStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.CexLetter

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem zc_eq_act (a : ℕ) : zc E a = act (Op.lie (fun i j => if i = j then 1 else 0) : Op E a) := rfl

theorem zc_mapsTo {a : ℕ} (π : CuspSub E a) : ∀ φ ∈ π.V, zc E a φ ∈ π.V := fun φ hφ => by
  rw [zc_eq_act]; exact π.stable _ φ hφ

theorem exists_scalar (x : Letter E) : ∃ c : ℂ, ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur E x.1 x.2 ((zc E x.1).restrict (zc_mapsTo x.2)) (by
    intro o φ
    apply Subtype.ext
    have := congrArg (fun f : Module.End ℂ (Sm E x.1) => f φ.1) ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).1 o)
    simpa [LinearMap.restrict_apply, CuspSub.op] using this)
  exact ⟨c, fun φ hφ => by simpa using congrArg Subtype.val (hc ⟨φ, hφ⟩)⟩

theorem cex_spec (x : Letter E) : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ := by
  unfold cex; exact Classical.epsilon_spec (exists_scalar x)

theorem cex_unique (x : Letter E) (c : ℂ) (h : ∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) : cex x = c := by
  obtain ⟨φ, hφ, hne, hc⟩ := h
  have h1 := cex_spec x φ hφ
  rw [hc] at h1
  exact (smul_left_injective ℂ hne h1).symm

theorem cex_tw (x : Letter E) (t : ℝ) : cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t := by
  obtain ⟨χ, h1, -, -, h4⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (t : ℂ)
  have hχ : χ = nu E t := by have := h4 (Complex.ofReal_im t); rwa [Complex.ofReal_re] at this
  subst hχ
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
  apply cex_unique
  refine ⟨mulChi x.1 (nu E t) φ, ?_, ?_, ?_⟩
  · exact ⟨φ, hφ, rfl⟩
  · exact fun h0 => hne ((mulChi x.1 (nu E t)).injective (h0.trans (map_zero _).symm))
  · show zc E x.1 (mulChi x.1 (nu E t) φ) = _
    rw [h1, cex_spec x φ hφ, ← add_smul, map_smul]
    rfl

theorem rexp_tw (x : Letter E) (hx : 1 ≤ x.1) (t : ℝ) : rexp (tw x t) = rexp x + t := by
  have hd : (0:ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha : (0:ℝ) < x.1 := by exact_mod_cast hx
  have hne : (x.1 : ℝ) * Module.finrank ℚ E ≠ 0 := (mul_pos ha hd).ne'
  unfold rexp
  rw [cex_tw]
  show (cex x + (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ)).re / ((x.1:ℝ) * Module.finrank ℚ E) = _
  rw [show (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ) = (((x.1:ℝ) * Module.finrank ℚ E * t : ℝ) : ℂ) by
    push_cast; ring, Complex.add_re, Complex.ofReal_re]
  field_simp

theorem cex_eq_zero_iff (x : Letter E) : cex x = 0 ↔ IsNormalised x.2 := by
  constructor
  · intro h φ hφ t g
    have := ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).2.2 φ 0).1 (by rw [← h]; exact cex_spec x φ hφ) t g
    simpa using this
  · intro hN
    obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
    exact cex_unique x 0 ⟨φ, hφ, hne, ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).2.2 φ 0).2 (fun t g => by simpa using hN φ hφ t g)⟩

end GlobalTheory.ResW.CexLetter

open GlobalTheory.ResW.CexLetter in

theorem GlobalTheory.ResW.letter_centralExponent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Letter E), (∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ) ∧ (∀ t : ℝ, cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t) ∧ (1 ≤ x.1 → ∀ t : ℝ, rexp (tw x t) = rexp x + t) ∧ (cex x = 0 ↔ IsNormalised x.2) ∧ ∀ c : ℂ, (∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) → cex x = c := by
  intro E _ _ _ x
  exact ⟨cex_spec x, cex_tw x, rexp_tw x, cex_eq_zero_iff x, fun c h => cex_unique x c h⟩
