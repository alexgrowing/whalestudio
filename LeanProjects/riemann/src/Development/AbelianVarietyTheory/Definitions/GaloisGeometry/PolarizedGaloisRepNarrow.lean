import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OddOrSlightlyRegIffOfEven
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrowT

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NarrowPolarizedGalois

open GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

abbrev SqIntSomewhere (π : CuspSub E a) : Prop := GalNarrow7.SqIntSomewhere π

abbrev IsWeightOf (π : CuspSub E a) (wt : ℤ) : Prop := GalNarrow7.IsWeightOf π wt

structure AboveN (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) → IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc →
      (∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
      ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0)

  sizeAbove : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) →
    ∀ (wt : ℤ) (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).lpTw ((wt : ℝ) / 2)).eig g,
    IsWeightOf π wt → ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧
      ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure PropsN (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ

  awaySS : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g

  awayFromResidueChar : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      wdOf h hl ι r = rc (algNorm σ)

  awayIne : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
    ∀ (n : ℕ) (x y : WDRep h (Fin n → ℂ)), WD.mk x = wdOf h hl ι r → WD.mk y = rc (algNorm σ) →
    ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y.ρ (ineIncl h s) v = χ s • v) → y.N v = 0) →
      ∀ v, (∀ s, x.ρ (ineIncl h s) v = χ s • v) → x.N v = 0

  sizeAway : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    (∃ σ, π.IsLocComp w σ ∧ ¬ SmGL.IsSpherical σ.ρ) → ∀ (g : Weil h), deg g ≠ 0 →
      ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  sqInt : SqIntSomewhere π → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w), (∀ (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      wdOf h hl ι r = rc (algNorm σ)) ∧ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ (τ : E →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (ι.toRingHom.comp τ) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveN π ι r HT P h Bw hj

end GlobalTheory.NarrowPolarizedGalois

namespace GlobalTheory.Published

def PolarizedGaloisRepNarrow : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      GalNarrowT.EverywhereGood π →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
        NarrowPolarizedGalois.PropsN π χ ι r wt HT

end GlobalTheory.Published

namespace GlobalTheory.NarrowPolarizedGalois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

example {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)}
    {HT : (E →+* Qbar l) → Multiset ℤ} {P : LocPrime l} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    {h : IsPlaceOver A w} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    {Bw : LocBridge l E Ω (Dec (F := E) A) O} {hj : Pst.Induces Bw} (L : AboveN π ι r HT P h Bw hj)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (hσ : π.IsLocComp w σ)
    (hI : PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥) (hs : SmGL.IsSpherical σ.ρ) :
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) := (L.iwahori σ hσ hI (Or.inr hs)).1

example (π : CuspSub E a) (wt : ℤ) : IsWeightOf π wt ↔ GalNarrow7.IsWeightOf π wt := Iff.rfl

example (π : CuspSub E 1) : GalNarrowT.EverywhereGood π := GalNarrowT.everywhereGood_rank_one π

end GlobalTheory.NarrowPolarizedGalois

end
