import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.TnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu

def AutOff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω)
    (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) : Prop :=
  ∀ (L : IntermediateField ℚ Ω) [NumberField L] [IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L →
    IsIrr (R.comp (resQ L)) → IsAutC ι (R.comp (resQ L))

def AutomorphyRankFour : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ → IrrOpen ρ →
    ∀ (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), g0 ∉ K'.fixingSubgroup →
    (∃ τ s, TauDat ι K' g0 (m * 1) c₁ τ s (κ ^ 1)) →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 9 ∧ ∀ (ρ₁ τ : G ℚ Ω →* M2 c₁.O) s, RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits →
      TauDat ι K' g0 (m * j) c₁ τ s (κ ^ j) → AutOff ι K' (tenB ρ₁ τ)

end UpperTheory.V.Cu

end
