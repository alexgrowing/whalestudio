import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def AtPlace (π : Submodule ℂ (UA E n → ℂ)) {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (w : HeightOneSpectrum (𝓞 E)) (P : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  GlobalTheory.SmGL.IsSubquotient P.ρ (locProd h w (σ · w)) ∧
  (IsUnramU π w → GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n)) ∧
  (∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w P.ρ (GlobalTheory.LGrp.bcParam n α)) ∧
  (IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ)

end GlobalTheory.PfBCI

end
