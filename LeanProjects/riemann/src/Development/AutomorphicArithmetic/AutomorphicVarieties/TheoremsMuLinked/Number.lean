import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Alg

namespace UpperTheory.V.Th

structure InpU : Prop extends U3.CohInp where
  lemM : LemmaM
  lemM' : LemmaM'
  lemP : LemmaP
  kato : Z.Kato.KatoTwo
  rigI : RigI
  rigII : RigII
  number : Af.CongruenceNumberRankThree

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws in

def SpPt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), Ctx2 D ∨ Ctx3 D →
    ∀ r, D.EPt r → Irr r → ∃ T : Tower D, T.Fit ∧ T.Deep ∧ ∀ c₁ : Coef l,
      ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l)
        (r₁ : G ℚ Ω →* M4 (PadicAlgCl l)), c₁.O ≤ c'.O ∧ IsConj4 r r₁ ∧ D.Mult r₁ ∧
        r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r ∧
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) ∧ Irr (r₁.comp T.L.fixingSubgroup.subtype)

end UpperTheory.V.Th

end
