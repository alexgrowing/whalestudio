import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.IsobaricBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure IsBaseChange (π : Submodule ℂ (UA E n → ℂ)) {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (m : Fin c → (E →+* ℂ) → Multiset ℂ)
    (P : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

  sub : ∀ w, GlobalTheory.SmGL.IsSubquotient (P w).ρ (locProd h w (σ · w))

  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (P w).ρ (GlobalTheory.LFun.KGL w n)

  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
    (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (P w).ρ (GlobalTheory.LGrp.bcParam n α)

  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (P w).ρ

  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

end GlobalTheory.IsobaricBC

namespace GlobalTheory.Published

def BaseChangeIsobaric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ)
        (P : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin n) (w.adicCompletion E))),
        IsobaricBC.IsBaseChange π h V σ m P

end GlobalTheory.Published

end
