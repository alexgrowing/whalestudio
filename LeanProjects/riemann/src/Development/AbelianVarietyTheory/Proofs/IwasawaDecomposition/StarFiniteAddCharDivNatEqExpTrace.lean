import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.CharRat

theorem star_psiEf_divN_inclE : ∀ (D : D7) (X : HidaSetting D) (α : 𝓞 D.host.E), star (X.psiEf (divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))))) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℂ) / ((X.B.g : ℕ) : ℂ)) := by
  intro D X α
  set y : X.B.I.E := X.ιE.symm (α : D.host.E) with hy
  set q : X.B.I.E := algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y with hq
  have hdiv : divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) q := by
    unfold divN
    rw [hq, map_mul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hgq : algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) = algebraMap ℚ X.B.I.E ((X.B.g : ℚ)⁻¹) := by
    rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
  have htrq : Algebra.trace ℚ X.B.I.E q = (X.B.g : ℚ)⁻¹ * Algebra.trace ℚ X.B.I.E y := by
    rw [hq, hgq, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have htr : Algebra.trace ℚ X.B.I.E y = Algebra.trace ℚ D.host.E (α : D.host.E) := by
    conv_rhs => rw [← X.ιE.apply_symm_apply (α : D.host.E)]
    exact (Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv y).symm
  have hint : ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (α : D.host.E) :=
    Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.E) (B := 𝓞 D.host.E) α
  rw [hdiv, eq_inv_of_mul_eq_one_left (X.psiEf_rat q), GlobalTheory.St.G.psiEinf_eq_exp_trace, htrq, htr, ← hint,
    ← Complex.exp_neg]
  change (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_ratCast]
  push_cast
  ring

end GlobalTheory.Mem.CharRat

end
