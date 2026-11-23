import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PublishedInputsThirdLayer

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
open Formalism.MainNotions.N Formalism.L2 Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem evLgG_field_of_small_field : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayer → EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    (∀ X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7, X.R.C = (TC.cf w.I w.l Z) → GlobalTheory.TwInputs.FieldOk X) ∧
    ∃ L : GlobalTheory.LamTie.LamDat (w.st Z).toD7, L.C = (TC.cf w.I w.l Z) ∧ L.Ok ∧ L.Teich ∧ L.q0 = AbsolutelyIrreducibleSpan.q0 (w.st Z).toD7 ∧
      ∀ a, (L.chi a).ValuesIn 0 (embLL0 (w.st Z).toD7) := by
  intro hP
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (lg_fieldOk hP.rayF K).imp fun B f _ hO h _ T w Z => ?_
  obtain ⟨-, h1, h2⟩ := h w.C Z.W Z.V Z.S Z.N Z.G
  rw [cf_eq_at]
  obtain ⟨L, a, b, c, d, e⟩ := h2 (auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO)
  exact ⟨h1, L, c, a, b, d, e⟩
end GlobalTheory.TwInputs.SmallField
end
end
