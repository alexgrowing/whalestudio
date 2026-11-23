import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

def SsCmp {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x y : WD h) : Prop :=
  AbW x ∨ AbW y → ∀ s, x.charPol s = y.charPol s

theorem SsCmp.of_eq {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} {x y : WD h} (e : x = y) : SsCmp x y := fun _ _ => by rw [e]

def SsCalc : Prop :=
  ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v),
    (∀ (n : ℕ) (x : WD h) (μ : Fin n → ↥(Weil h) →* ℂˣ), (∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) → AbW x) ∧
    (∀ x x' y y' : WD h, SsCmp x y → SsCmp x' y' → SsCmp (x.lpSum x') (y.lpSum y')) ∧
    ∀ x y z : WD h, z.lpDim = 1 → (SsCmp (x.lpChar z) (y.lpChar z) ↔ SsCmp x y)

def SsMove : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (x y : WD h) (x' y' : WD h'),
      WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → SsCmp x' y' → SsCmp x y

abbrev WO {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := IsWDOf ι r y

def CsdSs : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WO ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            SsCmp (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

theorem csdSs_of_full (H : GlobalTheory.Published.CaraianiLocalGlobalDual) : CsdSs := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hd hc
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha π hd hc
  refine ⟨R, h1, h2, h3, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  exact ⟨(h4 P AI hT w A h O Bw hj).1, fun σ hσ rc hrc => SsCmp.of_eq ((h4 P AI hT w A h O Bw hj).2 σ hσ rc hrc)⟩

end UpperTheory.V.Lev

end
