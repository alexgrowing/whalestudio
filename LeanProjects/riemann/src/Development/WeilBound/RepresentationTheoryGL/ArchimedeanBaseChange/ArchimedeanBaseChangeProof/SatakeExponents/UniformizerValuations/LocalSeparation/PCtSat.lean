import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSatB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpParabEqLevOpCt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ordL_unif {w : Pl E} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ordL ϖ = 1 := by
  have h1 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dif_neg h1]
  have e : WithZero.unzero h1 = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, hϖ]
  rw [e, toAdd_ofAdd, neg_neg]

theorem ord_neg_one' {w : Pl E} : GlobalTheory.SmGL.ord (w.adicCompletion E) (-1) = 0 := by
  rw [GlobalTheory.BCT.InertChar.ord_eq_ordL]
  have : Valued.v ((((-1 : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) = 1 := by simp
  have h1 : Valued.v ((((-1 : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) ≠ 0 := by rw [this]; exact one_ne_zero
  unfold ordL
  rw [dif_neg h1]
  have e : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, this]; rfl
  rw [e, toAdd_one, neg_zero]

theorem ordL_one' {w : Pl E} : ordL (1 : w.adicCompletion E) = 0 := by
  have h1 := GlobalTheory.BCT.InertChar.ord_eq_ordL w (1 : (w.adicCompletion E)ˣ)
  have h2 := GlobalTheory.SmGL.ord_mul (w.adicCompletion E) 1 1
  rw [mul_one] at h2
  rw [Units.val_one] at h1
  omega

theorem ordL_div' {w : Pl E} {x y : w.adicCompletion E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x / y) = ordL x - ordL y := by
  have := Formalism.UG.P.fIwasawa_ordL_mul (x / y) y (div_ne_zero hx hy) hy
  rw [div_mul_cancel₀ x hy] at this
  omega

end PositivityTheory.Rg.BcB.F.RS
