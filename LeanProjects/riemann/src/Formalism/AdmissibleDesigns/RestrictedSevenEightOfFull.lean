import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro
import Formalism.SharpRestriction.LevelLetterCocycles.QpowOfTw
import Formalism.LocalRingCardinality.SpanPowerMembership.Places

noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Rows

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

def AllDesignConditions : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
      (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
      GoodR D.nd i r → TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → LargeLevelLemmas.adm51 i r ρ π

def SomeDesignCondition : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
      (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
      TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → LargeLevelLemmas.adm51 i r ρ π

def UnrInAll : Prop :=
  ∀ (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    Formalism.WeaklyAdmissibleFiltrations.Z1ur (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw)
              ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) (Br.inert D.nbr i w hw) ≤
      Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (Br.PD D.loc D.nbr i w hw)
        (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)

def BKaAll : Prop := ∀ i : D.nd.Loc, LargeLevelLemmas.BlochKatoAnnihilators i

def FinAll : Prop := ∀ i : D.nd.Loc, LargeLevelLemmas.tateH1FinitenessAtPlacesOver i

def SelfGoodAll : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).IsGood

def QPowAll : Prop :=
  ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n

def Rows : Prop :=
  AllDesignConditions D ∧ UnrInAll D ∧ BKaAll D ∧ FinAll D

def MainBoundForDesign : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB

def SecondMainBoundForDesign : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → LargeLevelLemmas.admitted i r ρ π → LargeLevelLemmas.Conclusion1 i r ρ π dc lenRow e' cB

def PurityConditionsForDesign : Prop :=
  ∀ (ep : Bool) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB

end Formalism.MainNotions.N.K.Rows

end
