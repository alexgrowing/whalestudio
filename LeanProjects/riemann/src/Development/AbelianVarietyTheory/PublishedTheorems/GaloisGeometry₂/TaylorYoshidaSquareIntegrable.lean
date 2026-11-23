import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def TaylorYoshidaSquareIntegrable : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → (CG.mk π).IsRegAlg →
    (∃ (x : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (x.adicCompletion E))), π.IsLocComp x σ ∧
      UnitaryDual.IsSquareIntegrable (IrrGL.of σ.ρ σ.smooth σ.irred)) →
    (∃ R : G E Ω →* GL (Fin a) (Qbar l), CarHyp.IsAssoc π ι R) ∧
    ∀ R : G E Ω →* GL (Fin a) (Qbar l), CarHyp.IsAssoc π ι R →
      (∀ (v : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A v),
        (∀ rc : IrrGL (v.adicCompletion E) → WD h, TheRec.IsTheRec h rc → ∀ σ σ', π.IsLocComp v σ →
          Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → wdOf h hl ι R = rc (algNorm σ')) ∧
        ((wdOf h hl ι R).lpTw (((a : ℝ) - 1) / 2)).tempered) ∧
      ((∃ x : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ x.asIdeal ∧ ∃ σ : SmIrr (GL (Fin a) (x.adicCompletion E)),
          π.IsLocComp x σ ∧ UnitaryDual.IsSquareIntegrable (IrrGL.of σ.ρ σ.smooth σ.irred)) →
        UpperTheory.V.Af.IsIrr R) ∧
      (∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c → IsConjDual c R (cycBar E Ω l ^ (1 - (a : ℤ)))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
        IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧
        IsdRAt P Bw (R.comp (Dec (F := E) A).subtype) ∧
        (∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (R.comp (Dec (F := E) A).subtype)) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 + z) →
          IsJumpsAt P Bw (R.comp (Dec (F := E) A).subtype) τ J

end GlobalTheory.Published

end
