import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1SubstEqPull2OfIsHomStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem cob1_defect_and_defect_mul_of_isLaw : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ),
    cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧
    defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  intro O E _ _ _ d μ hμ f m n
  obtain ⟨hL, hmap⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E (algebraMap O E)
  have hup : ∀ k, up E (nmul μ k) = nmul (up E μ) k := fun k =>
    funext fun i => (hmap k i).2
  have hc : ∀ i, constantCoeff (up E μ i) = 0 := hL.const
  have hk : ∀ k, HasSubst (up E (nmul μ k)) := fun k =>
    hasSubst_of_constantCoeff_zero fun i => by
      rw [hup k]; exact ((GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL 0 k).1 i)
  have hsub : ∀ a b : MvPowerSeries (Fin d) E, cob1 (up E μ) (a - b) = cob1 (up E μ) a - cob1 (up E μ) b :=
    fun a b => by rw [eq_sub_iff_add_eq, ← formalCoboundary_add hc, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · unfold defect
    rw [hsub, formalCoboundary_smul hc, hup n]
    rw [GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom E d (up E μ) (up E μ) (nmul (up E μ) n) hc hc (GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple E d (up E μ) hL n) f]
  · have hcomp : subst (up E (nmul μ n)) (subst (up E (nmul μ m)) f) = subst (up E (nmul μ (m * n))) f := by
      rw [subst_comp_subst_apply (hk m) (hk n)]
      congr 1
      funext i
      rw [hup, hup, hup, (GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL m n).2.2.1 i]
    unfold defect
    rw [subst_sub (hk n), subst_smul (hk n), hcomp, smul_sub, Nat.cast_mul, mul_smul]
    abel

end GlobalTheory.QLog
