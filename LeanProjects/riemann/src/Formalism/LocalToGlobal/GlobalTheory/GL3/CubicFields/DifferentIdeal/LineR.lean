import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

def mmR {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M] {ι : Type}
    (emb : ι → E →+* ℂ) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 M) (ι → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (I : Submodule (𝓞 E) E), v = fun i => liftM M (emb i a)}

def lineR {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M] {ι : Type}
    [DecidableEq ι] (emb : ι → E →+* ℂ) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (i : ι) : Submodule (𝓞 M) M :=
  (mmR M emb I).comap (LinearMap.single (𝓞 M) (fun _ : ι => (M : Type)) i)

def imI {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 M) M :=
  Submodule.span (𝓞 M) {y | ∃ a ∈ (J : Submodule (𝓞 E) E), y = liftM M (σ a)}

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
