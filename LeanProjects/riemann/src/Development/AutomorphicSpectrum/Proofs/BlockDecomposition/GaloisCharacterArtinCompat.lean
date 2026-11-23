import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HeckeLocal

theorem isLAdicOf_localIdele {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (μ : G E Ω →* (Qbar l)ˣ) (h : IsLAdicOf art ι χ n μ) (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) (σ : G E Ω) (hx : art (localIdele E w x) = toAb E Ω σ) :
    ((μ σ : (Qbar l)ˣ) : Qbar l) =
      ι.symm (((χ.1 (localIdele E w x) : ℂˣ) : ℂ)) * locPow ι n w (x : w.adicCompletion E) := by
  rw [h _ σ hx, infPow_localIdele, inv_one, mul_one, lPow_localIdele]

end GlobalTheory.CompanionTheory.HeckeLocal

end
