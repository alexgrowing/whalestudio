import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT.Model

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isRecT_of_isRec (hT : GlobalTheory.Published.DepthZeroTypeInertia) {rc : IrrGL (w.adicCompletion E) → WD h}
    (hrec : IsRec h rc) : IsRecT h rc := by
  obtain ⟨a, ha, ε, hε, H⟩ := hrec
  refine ⟨a, ha, ?_⟩
  exact
    { dim := H.dim
      one := H.one
      langlands := fun l x hx => H.langlands l x hx
      cusp := fun x hx => (H.cusp x).1 hx
      nu := fun x s => H.nu_eq x s
      absCentral := fun x ω hω σ => by rw [H.central x ω hω σ]
      twist := fun x χ hχ _ => H.twist x χ hχ
      central := fun x ω _ hω => H.central x ω hω
      dual := fun n π π' _ e => H.dual n π π' e
      inj := fun x y _ hxy => H.bij.1 hxy
      depth := fun x _ hx => (H.depth x).1 hx
      type := by
        intro E' _ _ _ _ _ _ g _ w' h'
        exact hT E E' Ω g A w h w' h' rc ⟨a, ha, ε, hε, H⟩ }

theorem recTExists_of (hL : GlobalTheory.Published.LocalLanglandsGL) (hT : GlobalTheory.Published.DepthZeroTypeInertia) : RecTExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨rc, hrc, -⟩ := hL.1 E Ω A w h
  exact ⟨rc, isRecT_of_isRec hT hrc⟩

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL k} (hx : Toral x) : Good x := by
  obtain ⟨s, hs, hy⟩ := hx
  exact ⟨s, hs, fun y hys => Or.inl (hy y hys)⟩

end Classes

end GlobalTheory.RecT.Model

end
