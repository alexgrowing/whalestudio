import Mathlib
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.CrystallineUnitParts.ConradLocalTiedness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoldsFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ExistsPrimeNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace CompanionTheory.PRW.ACWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

def expo (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (w : HeightOneSpectrum (𝓞 E))
    (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}) : ℤ :=
  n ((ι.toRingHom.comp j.1).comp (algebraMap E (w.adicCompletion E)))

def unitPart (w : HeightOneSpectrum (𝓞 E)) (π x : (w.adicCompletion E)ˣ) : (w.adicCompletion E)ˣ :=
  x * π ^ (-GlobalTheory.SmGL.ord (w.adicCompletion E) x)

end CompanionTheory.PRW.ACWD

end
