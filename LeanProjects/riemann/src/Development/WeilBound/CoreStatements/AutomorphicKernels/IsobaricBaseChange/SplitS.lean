import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.AtPlace

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem split_component {π : Submodule ℂ (UA E n → ℂ)} {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    {w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt w) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hsub : GlobalTheory.SmGL.IsSubquotient P.ρ (locProd h w (σ · w)))
    (hsph : IsUnramU π w → GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n))
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) : AtPlace π h σ w P := by
  exact ⟨hsub, hsph, fun _ _ _ hconj hinv _ _ => absurd hs (GlobalTheory.BcSpehCompare.not_isSplitAt hconj hinv.2.1), fun _ => hc⟩

end GlobalTheory.PfBCI

end
