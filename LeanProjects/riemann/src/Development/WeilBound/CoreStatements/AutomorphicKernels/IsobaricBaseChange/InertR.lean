import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem inert_of_not_unram {π : Submodule ℂ (UA E n → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsUnramU π w)
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) :
    ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w P.ρ (GlobalTheory.LGrp.bcParam n α) := by
  intro s ϖ q hs hinv α hα
  exact absurd (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt hs hinv.2.1 hα) hw

end GlobalTheory.PfBCI

end
