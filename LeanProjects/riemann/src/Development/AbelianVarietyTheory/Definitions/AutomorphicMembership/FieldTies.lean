import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.AtMember

variable {D : D7}

structure CorePin (J : Core D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop where
  laws : LawsCore J
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  pb : J.pb = pb

theorem CorePin.reCore {J : CoreJ D} {pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)} (h : CorePin J.toCore pb) {dict mu chiW x₀ cE}
    (hM : LawsM (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore) : CorePin (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore pb :=
  ⟨⟨hM, h.laws.cuspMul, h.laws.latZ, h.laws.cuNe, h.laws.expo⟩, h.canon, h.rank, h.pb⟩

structure FieldTies (D : D7) (C : Formalism.L2.Host.CharFrame D) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  del : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  del' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D
  small : ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

def HalfAt (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def NumAtL (L : SizeData₂ D) (x : ℝ) : Prop :=
  DV.KapDef D ∧ (∃ (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), GlobalTheory.BigOn.PageNum Tp x) ∧ FieldSmall D L

end GlobalTheory.AtMember
