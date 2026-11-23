import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

def KatoTwoW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (e N : ℕ) (θ ψ : G ℚ Ω →* (Qbar l)ˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Used l Ω K e N θ ψ W →
    ∀ (ι : Qbar l ≃+* ℂ) (f : Af.Newform (2 * e + 1)), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → WitAQ ι W →
      Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ))

example : type_of% @KatoTwo := @KatoTwoW

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

theorem kUse (hK : KatoTwo) (D : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ) (h : D.IsModular ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf

theorem kUse' (hK : KatoTwoW) (_ : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ)
    (h : (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.1.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf h.2

end UpperTheory.V.Z.Kato.WeilSphericalRecords
