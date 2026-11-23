import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ScholzeFunctorialExtension

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt.LbcModel

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)}

theorem lbc_ofChar_one (f : v.adicCompletion K →+* u.adicCompletion L) (hf : Continuous f)
    (hK : ∀ z : K, f (algebraMap K _ z) = algebraMap L _ (algebraMap K L z))
    (hd : letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
      0 < Module.finrank (v.adicCompletion K) (u.adicCompletion L)) :
    lbc K L v u (IrrGL.ofChar (1 : (v.adicCompletion K)ˣ →* ℂˣ) isSmoothChar_one)
      (IrrGL.ofChar (1 : (u.adicCompletion L)ˣ →* ℂˣ) isSmoothChar_one) :=
  by
  refine ⟨f, hf, hK, ?_⟩
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
  exact fun s _ => ⟨1, _, _, rfl, rfl, LBC.isLBC_one s hd⟩

theorem lbc_deg (x : IrrGL (v.adicCompletion K)) (X : IrrGL (u.adicCompletion L)) (h : lbc K L v u x X)
    (hs : ∀ f : v.adicCompletion K →+* u.adicCompletion L,
      letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
      ∃ s : u.adicCompletion L ≃ₐ[v.adicCompletion K] u.adicCompletion L, s ≠ 1) : x.1 = X.1 := by
  obtain ⟨f, -, -, H⟩ := h
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
  obtain ⟨s, hs1⟩ := hs f
  obtain ⟨m, π, P, rfl, rfl, -⟩ := H s hs1
  rfl

theorem feeds (hS : GlobalTheory.Published.ScholzeFunctorialExtension) : ∃ σ : SigFam,
    ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
      [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
      (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A u)
      (x : IrrGL (v.adicCompletion K)) (X : IrrGL (u.adicCompletion L)), x.IsCusp → lbc K L v u x X →
      (∀ f : v.adicCompletion K →+* u.adicCompletion L,
        letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
        (Module.finrank (v.adicCompletion K) (u.adicCompletion L)).Prime ∧
          ∃ s : u.adicCompletion L ≃ₐ[v.adicCompletion K] u.adicCompletion L, s ≠ 1) →
      GlobalTheory.LocLanglands.WDRel (RingEquiv.refl Ω) (σ K Ω A v h x) (σ L Ω A u h' X) := by
  obtain ⟨σ, -, -, H⟩ := hS
  refine ⟨σ, fun K L Ω _ _ _ _ _ _ _ _ _ _ _ A v u h h' x X hx hl hp => ?_⟩
  obtain ⟨f, hf, hK, hB⟩ := hl
  exact H K L Ω A v u h h' f hf hK (hp f).1 (hp f).2 x X hx hB

end GlobalTheory.FunExt.LbcModel
