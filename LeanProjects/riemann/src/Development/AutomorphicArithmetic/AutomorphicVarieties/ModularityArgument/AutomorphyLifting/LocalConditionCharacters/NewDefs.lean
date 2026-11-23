import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base

namespace UpperTheory.V.Z.Win.RR

def WitUp {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : IsAbelianGalois ℚ L) (_ : Algebra L Ω),
      IsIrr (W.comp (galEmb ℚ L Ω)) ∧
      (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) ∧
      ∃ ka : G L Ω →* (Qbar l)ˣ, Sd.IsAlgChar ι ka ∧ WitA ι (tw (W.comp (galEmb ℚ L Ω)) ka)

def AutNewformA : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → IsIrr W → IsAutR ι W → WitUp ι W →
    ∀ (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 → ∀ (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) →
    IsFlagOn W (H ⊓ Ine (F := ℚ) B) (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype) →
    ∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))

end UpperTheory.V.Z.Win.RR
