import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def GlobalTheory.Published.LocalGlobalAboveLPst : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → GKCoh.IsCohomological π →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} {π : CuspSub E a}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
  {P : LocPrime l} {AI : LocAinf l P} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem GlobalTheory.GalOfCusp.IsGalRepOf.isPstAt {χ : HChar (maximalRealSubfield E)} (hG : IsGalRepOf π χ ι r wt HT)
    (hB : GlobalTheory.Published.DeRhamPotSemistable) (T : LocTied l P AI) (h : IsPlaceOver A w)
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) :=
  hB.isPstAt T Bw _ (Units.continuous_val.comp (hG.cont.comp continuous_subtype_val))
    (hG.above P AI ⟨T⟩ w A h O Bw hj).deRham

theorem GlobalTheory.Published.LocalGlobalAboveL.pst_and_wdAt (H : GlobalTheory.Published.LocalGlobalAboveL) (hB : GlobalTheory.Published.DeRhamPotSemistable)
    (ha : 2 ≤ a) (hc : π.IsCsd) (hcoh : GKCoh.IsCohomological π) (hG : IsGalRepOf π (quadChar E ^ a) ι r wt HT)
    (T : LocTied l P AI) (h : IsPlaceOver A w) (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
      wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ) :=
  ⟨hG.isPstAt hB T h Bw hj, H E Ω l ι a ha π hc hcoh r wt HT hG P AI ⟨T⟩ w A h O Bw hj⟩

end

theorem GlobalTheory.Published.LocalGlobalAboveL.regAlg (H : GlobalTheory.Published.LocalGlobalAboveL) (hC : GlobalTheory.Published.RegularAlgebraicPurity) :
    GlobalTheory.GalOfCusp.LocalGlobalAboveL :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w _ A h O _ _ _ Bw hj σ hσ rc hrc =>
    H E Ω l ι a ha π hc (hC E a (by omega) π hr).2 r wt HT hG P AI hT w A h O Bw hj σ hσ rc hrc

theorem GlobalTheory.Published.LocalGlobalAboveLPst.of_classicalTheorems (H : GlobalTheory.Published.LocalGlobalAboveL) (hB : GlobalTheory.Published.DeRhamPotSemistable) :
    GlobalTheory.Published.LocalGlobalAboveLPst :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ha _ hc hcoh _ _ _ hG _ _ ⟨T⟩ _ _ h _ _ _ _ Bw hj => H.pst_and_wdAt hB ha hc hcoh hG T h Bw hj

theorem GlobalTheory.Published.LocalGlobalAboveLPst.localGlobalAboveL (H : GlobalTheory.Published.LocalGlobalAboveLPst) :
    GlobalTheory.Published.LocalGlobalAboveL :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh r wt HT hG P AI hT w A h O _ _ _ Bw hj =>
    (H E Ω l ι a ha π hc hcoh r wt HT hG P AI hT w A h O Bw hj).2

end
