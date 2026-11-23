import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.GLp.Supp

open GlobalTheory.SmGL GlobalTheory.PRep ValuativeRel

theorem valuation_units_map_eq_one {g : ℕ} [Fact g.Prime] (u : ℤ_[g]ˣ) :
    valuation ℚ_[g] ((Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u : ℚ_[g]ˣ) : ℚ_[g]) = 1 := by
  have hn : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.isUnit_iff.1 u.isUnit
  have e : ((Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u : ℚ_[g]ˣ) : ℚ_[g]) = ((u : ℤ_[g]) : ℚ_[g]) := rfl
  rw [e]
  refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
  · have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 ((u : ℤ_[g]) : ℚ_[g])).1 (by simpa using hlt)
    simp [hn] at this
  · have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g ((u : ℤ_[g]) : ℚ_[g]) 1).1 (by simpa using hlt)
    simp [hn] at this

theorem mapsToProd_of_jac₂ : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ) (h : a + b = n) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (φ : (GlobalTheory.SmGL.jac₂ (GlobalTheory.SmGL.stdSum h) π).IntertwiningMap (GlobalTheory.SmGL.extTensor σ ρ)), φ ≠ 0 →
    Supp.MapsToProd π σ ρ := by

  intro g _ a b n h V W W' _ _ _ _ _ _ π σ ρ φ hφ
  refine ⟨h.symm, absPow ℚ_[g] ((b : ℂ) / 2), absPow ℚ_[g] (-(a : ℂ) / 2),
    φ.toLinearMap ∘ₗ (twKer π (unipRad ℚ_[g] (two (stdSum h))) 1).mkQ, fun u => isUnram_absPow ℚ_[g] _ _ (valuation_units_map_eq_one u),
    fun u => isUnram_absPow ℚ_[g] _ _ (valuation_units_map_eq_one u), ?_, ?_⟩
  · intro hΛ
    apply hφ
    ext x
    exact LinearMap.congr_fun hΛ x
  · intro p x y h0 hx hy v
    have hp : p ∈ parab ℚ_[g] (two (stdSum h)) := by
      rw [mem_parab_iff]
      rintro (_|_) (_|_) i j hlt
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · apply h0
        · show ((stdSum h (Sum.inl j) : Fin n) : ℕ) < a
          rw [stdSum_inl]; exact j.isLt
        · show a ≤ ((stdSum h (Sum.inr i) : Fin n) : ℕ)
          rw [stdSum_inr]; omega
      · exact absurd hlt (by decide)
    have hl : leviProj ℚ_[g] (two (stdSum h)) ⟨p, hp⟩ = leviTwo ℚ_[g] (Fin a) (Fin b) (x, y) := by
      funext c
      cases c
      · refine Units.ext (Matrix.ext fun i j => ?_)
        rw [leviProj_apply]
        show _ = (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j
        have hi : (i : ℕ) < n := by omega
        have hj : (j : ℕ) < n := by omega
        rw [hx]
        simp only [Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
        rfl
      · refine Units.ext (Matrix.ext fun i j => ?_)
        rw [leviProj_apply]
        show _ = (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j
        have hi : a + (i : ℕ) < n := by omega
        have hj : a + (j : ℕ) < n := by omega
        rw [hy]
        simp only [Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
        rfl
    obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip ℚ_[g] (two (stdSum h)) ⟨p, hp⟩
    rw [hl] at hpu
    have hpu' : p = leviEmb ℚ_[g] (two (stdSum h)) (leviTwo ℚ_[g] (Fin a) (Fin b) (x, y)) * u := hpu
    have hmk : (Submodule.Quotient.mk (π u v) : Jacquet π (unipRad ℚ_[g] (two (stdSum h)))) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      refine Submodule.subset_span ⟨⟨u, hu⟩, v, ?_⟩
      simp
    have key : ∀ (M : Levi ℚ_[g] (Two (Fin a) (Fin b))) (w : V),
        (Submodule.Quotient.mk (π (leviEmb ℚ_[g] (two (stdSum h)) M) w) : Jacquet π (unipRad ℚ_[g] (two (stdSum h)))) =
          (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) M : ℂ) • jac (two (stdSum h)) π M (Submodule.Quotient.mk w) := by
      intro M w
      rw [jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
    have hint := Representation.IntertwiningMap.isIntertwining _ _ φ (x, y) (Submodule.Quotient.mk v : Jacquet π (unipRad ℚ_[g] (two (stdSum h))))
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
    change _ • φ (jac₂ (stdSum h) π (x, y) (Submodule.Quotient.mk v)) = _
    rw [hint, deltaHalf_two]
    simp only [Fintype.card_fin]
    rfl

end GlobalTheory.GLp.Supp
