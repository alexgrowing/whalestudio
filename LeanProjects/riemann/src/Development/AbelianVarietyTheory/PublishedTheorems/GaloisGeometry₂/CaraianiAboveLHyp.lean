import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CarHyp

open GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure IsAssoc (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop where
  cont : Continuous R
  ss : IsSSRep R
  unr : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ σ', π.IsLocComp w σ → SmGL.IsSpherical σ.ρ →
    Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → wdOf h hl ι R = rc (algNorm σ')

def IsTheRep (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  IsAssoc π ι R ∧ ∀ R' : G E Ω →* GL (Fin a) (Qbar l), IsAssoc π ι R' →
    ∃ p : GL (Fin a) (Qbar l), ∀ g, R' g = p * R g * p⁻¹

end GlobalTheory.CarHyp

namespace GlobalTheory.Published

def CaraianiAboveLHyp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∀ R : G E Ω →* GL (Fin a) (Qbar l), CarHyp.IsTheRep π ι R →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) →
      ∀ σ σ', π.IsLocComp w σ → Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → ∀ rc, TheRec.IsTheRec h rc →
        wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ')

end GlobalTheory.Published

end
