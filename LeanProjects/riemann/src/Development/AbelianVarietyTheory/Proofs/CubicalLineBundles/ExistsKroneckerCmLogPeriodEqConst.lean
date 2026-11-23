import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LamF

theorem exists_kronecker_logOm_re (E : Type) [Field E] [NumberField E] {d d' : ℕ} (h : d' = d) [Fact d.Prime]
    [NeZero d] (hd : d % 4 = 3) :
    ∃ (_ : NeZero d') (χ : DirichletCharacter ℂ d'), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) -
        (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) 1 /
          DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) 1).re := by
  subst h
  exact ⟨inferInstance, _, isKroneckerChar_quadraticChar hd, by
    rw [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]⟩

theorem exists_kronecker_logOm_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D,
    ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d),
      IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  intro D Q hp large₂
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd : D.host.d % 4 = 3 := by
    have := Q.H.d_mod
    rw [hp.1] at this
    omega
  obtain ⟨i, χ, hχ, e⟩ := exists_kronecker_logOm_re D.host.E hp.1 hd
  refine ⟨i, χ, hχ, e.trans ?_⟩
  have hv : 2 * Real.pi / rootDiscr D.host.E = Real.pi / D.host.v := by
    rw [Formalism.BasicNotions.Host.v, Formalism.BasicNotions.Host.rdE, rootDiscr_def, Int.cast_abs, one_div, div_div_eq_mul_div, mul_comm]
  rw [hv, SizeData₂.logOm, large₂.logDerivative_at_one_eq]
  rfl

end GlobalTheory.LamF
