import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
namespace UpperTheory.GalN.V
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
theorem mod0'_alt (h : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) : ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) := h.1
theorem witAQ_of_isModularA (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : Continuous W) (_ : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (_ : 1 ≤ e)
    (h : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) : _root_.UpperTheory.V.Z.Win.WitAQ ι W := h.2
end
theorem adm2B_of_adm2B (_ : _root_.UpperTheory.V.Af.Hypotheses') (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (_ : l ≠ 2) (ι : Qbar l ≃+* ℂ) (e M : ℕ) (_ : 1 ≤ e) (ρ : G K Ω →* GL (Fin 3) (Qbar l))
    (h : _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M ρ) : _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M ρ := h
end UpperTheory.GalN.V
end
end
