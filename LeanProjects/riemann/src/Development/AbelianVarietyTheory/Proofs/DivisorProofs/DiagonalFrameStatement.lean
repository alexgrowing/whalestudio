import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplicationStatement

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagAH

theorem conj_eq_of_totallyReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (φ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (φ x) = φ x := by
  have h : ComplexEmbedding.IsReal φ :=
    (NumberField.InfinitePlace.isReal_mk_iff).1 (IsTotallyReal.isReal _)
  rw [← ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.isReal_iff.1 h]

theorem exists_int_ne {F : Type} [Field F] [NumberField F] {φ ψ : F →+* ℂ} (h : φ ≠ ψ) :
    ∃ a : 𝓞 F, φ (a : F) ≠ ψ (a : F) := by
  by_contra hall
  push_neg at hall
  exact h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun a ↦ hall a))

theorem eq_diagonal_of_comm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) ℂ) (hH : Hm.IsHermitian) (e : Fin n → (F →+* ℂ)) (he : Function.Injective e)
    (h : ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F))) :
    Hm = Matrix.diagonal fun j ↦ ((Hm j j).re : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    have := congrFun (congrFun hH i) i
    simp only [Matrix.conjTranspose_apply] at this
    exact (Complex.conj_eq_iff_re.1 this).symm
  · rw [Matrix.diagonal_apply_ne _ hij]
    obtain ⟨a, ha⟩ := exists_int_ne (he.ne hij)
    have h1 := h a i j
    rw [conj_eq_of_totallyReal] at h1
    have h2 : (e i (a : F) - e j (a : F)) * Hm i j = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

theorem diagFrame : DiagFrame := by
  intro F _ _ _ 𝔠 X c hc u e he hact
  obtain ⟨u', Hm, χ, hex, hAH⟩ := GlobalTheory.T.exists_appell_humbert_uniformization F 𝔠 X c hc u
  have hact' : ∀ (a : 𝓞 F) w, u'.ex (fun j ↦ e j (a : F) * w j) = u'.ex w ≫ X.rm.act a := by
    rw [hex]; exact hact
  have hsym := GlobalTheory.T.appell_humbert_real_multiplication F 𝔠 X c hc u' e hact' Hm χ hAH
  have hdiag := eq_diagonal_of_comm Hm hAH.1 e he hsym
  refine ⟨u', fun j ↦ (Hm j j).re, hex, χ, ?_⟩
  rw [← hdiag]
  exact hAH

end GlobalTheory.DiagAH
