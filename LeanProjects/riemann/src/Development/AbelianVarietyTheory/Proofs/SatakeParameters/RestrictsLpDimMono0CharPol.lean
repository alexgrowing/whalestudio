import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem restricts_lpDim_mono0_charPol : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L]
    [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (x : WD h) (x' : WD h'), Restricts x x' →
    x'.lpDim = x.lpDim ∧ (x'.mono0 ↔ x.mono0) ∧ ∀ (σ : Weil h) (σ' : Weil h'),
      (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → x'.charPol σ' = x.charPol σ := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' x x' hr
  obtain ⟨n, a, b, rfl, rfl, hN, hρ⟩ := hr
  refine ⟨by rw [WD.lpDim_mk, WD.lpDim_mk], by rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, hN], fun σ σ' hs => ?_⟩
  rw [WD.charPol_mk, WD.charPol_mk, hρ σ σ' hs]

end GlobalTheory.AboveL
