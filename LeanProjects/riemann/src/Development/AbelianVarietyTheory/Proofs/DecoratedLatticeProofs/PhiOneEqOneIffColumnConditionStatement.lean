import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnCondition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_one_eq_one_iff_column_condition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (K : Type) [Field K] (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E), d.Ok → d'.Ok →
    d.N = Formalism.L2.Col.stdLat E a → d'.N = Formalism.L2.Col.stdLat E b →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    ∀ x : Formalism.L2.Col.HomE E a b, (Formalism.L2.Col.phiT K d d' x = 1 ↔ ∀ P : ST, ColCond P.1 t x) := by
  first | exact @GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond | exact GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond | (intros; apply GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond <;> assumption)
