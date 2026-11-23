import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegFlFlagMapRenamePerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernRootSubstitutionWeightLineBundleEqLinRoot
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := rfl

theorem degFl_rho_antisymm (H : Host E) (Dw : Datum H) (Q : MvPolynomial (Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (rho H Dw (antisymm Q)) =
      (∏ τ, ((Dw.mult τ).factorial : ℝ)) * Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (rho H Dw Q) := by
  rw [rho_eq_flagMap]
  unfold GlobalTheory.GoodMetric.antisymm
  rw [map_sum, ← GlobalTheory.Schubert.flagLin_apply, map_sum]
  have hterm : ∀ w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)),
      GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw
        ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)) • rename (fun x : Root Dw.mult =>
          (⟨x.1, w x.1 x.2⟩ : Root Dw.mult)) Q)) =
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
    intro w
    rw [map_zsmul, map_zsmul, GlobalTheory.Schubert.flagLin_apply,
      GlobalTheory.Schubert.degFl_flagMap_rename_perm, zsmul_eq_mul, ← mul_assoc]
    have hs : ((((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ)) *
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    rw [hs, one_mul]
  rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_pi]
  push_cast
  simp only [Fintype.card_perm, Fintype.card_fin]

theorem prod_factorial_mult (H : Host E) (Dw : Datum H) :
    (∏ τ, ((Dw.mult τ).factorial : ℝ)) =
      ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  have e1 : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.p.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  have e2 : ∀ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((Dw.mult τ.1).factorial : ℝ) = Dw.q.factorial := by
    intro τ; simp [Datum.mult, τ.2]
  simp only [e1, e2, Finset.prod_const, Finset.card_univ, mul_pow]
  congr 2
  exact Fintype.card_congr
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) }

theorem intGr_eq_flagDeg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (D : ℕ),
    D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) →
    antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) =
      chernRoots Dw.mult R * rootDiscr Dw.mult →
    intGr H Dw R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) := by
  intro E _ _ _ H Dw la R D hD hA
  unfold intGr
  rw [← hA, degFl_rho_antisymm, prod_factorial_mult, map_pow, rho_eq_flagMap,
    GlobalTheory.Schubert.chernRootSubstitution_weightLineBundle_eq_linRoot, hD]
  have hpos : ((Dw.p.factorial * Dw.q.factorial : ℝ)) ^ Fintype.card (GlobalTheory.AllWt.Psi H) ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  rw [mul_div_cancel_left₀ _ hpos]
  rfl

end GlobalTheory.GrassTop
