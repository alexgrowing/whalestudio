import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.NormVEqPowResF

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst
open PositivityTheory.Pf1.CLGD.DescRes

namespace LocalGlobalAboveLAlt

def RelIneAb : Prop := AtAll fun {E _} _ _ _ _ _ {A _} h => ∀ x y : WD h, Rel x y →
  (∀ g : ↥(Weil h), (g : G E _) ∈ ⁅Ine (F := E) A, Ine (F := E) A⁆ → Triv y g) →
    ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

def TempRes : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
    [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E'))
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (x : WD h) (s : ℝ),
    ((WD.res h h' x).lpTw s).tempered ↔ (x.lpTw s).tempered

def TemperednessTransfer : Prop := Glob fun x y => ∀ s : ℝ, (y.lpTw s).tempered → (x.lpTw s).tempered

end LocalGlobalAboveLAlt
