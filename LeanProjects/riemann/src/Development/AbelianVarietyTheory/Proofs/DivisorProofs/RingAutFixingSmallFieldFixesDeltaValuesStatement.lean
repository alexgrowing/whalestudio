import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  first | exact @GlobalTheory.DeltaFixed.aut_fixes_delta_values | exact GlobalTheory.DeltaFixed.aut_fixes_delta_values | (intros; apply GlobalTheory.DeltaFixed.aut_fixes_delta_values <;> assumption)
