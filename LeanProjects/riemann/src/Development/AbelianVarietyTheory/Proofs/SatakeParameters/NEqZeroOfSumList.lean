import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.NoTwHom

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def IsTw {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (f : V →ₗ[ℂ] V') : Prop :=
  ∀ (σ : Weil h) (v : V), f ((((normV w : ℕ) : ℂ) ^ deg σ) • a.ρ σ v) = b.ρ σ (f v)

def NoTw (X Y : WD h) : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V'),
    WD.mk a = X → WD.mk b = Y → ∀ f : V →ₗ[ℂ] V', IsTw a b f → f = 0

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

theorem IsTw.inl {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a1 : WDRep h V} {a2 : WDRep h V2} {b : WDRep h V'} {g : V × V2 →ₗ[ℂ] V'}
    (hg : IsTw (a1.sum a2) b g) : IsTw a1 b (g ∘ₗ LinearMap.inl ℂ V V2) := by
  intro σ v
  have : LinearMap.inl ℂ V V2 ((((normV w : ℕ) : ℂ) ^ deg σ) • a1.ρ σ v) =
      (((normV w : ℕ) : ℂ) ^ deg σ) • (a1.sum a2).ρ σ (LinearMap.inl ℂ V V2 v) := by
    ext <;> simp
  rw [LinearMap.comp_apply, this, hg]; rfl

theorem IsTw.inr {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a1 : WDRep h V} {a2 : WDRep h V2} {b : WDRep h V'} {g : V × V2 →ₗ[ℂ] V'}
    (hg : IsTw (a1.sum a2) b g) : IsTw a2 b (g ∘ₗ LinearMap.inr ℂ V V2) := by
  intro σ v
  have : LinearMap.inr ℂ V V2 ((((normV w : ℕ) : ℂ) ^ deg σ) • a2.ρ σ v) =
      (((normV w : ℕ) : ℂ) ^ deg σ) • (a1.sum a2).ρ σ (LinearMap.inr ℂ V V2 v) := by
    ext <;> simp
  rw [LinearMap.comp_apply, this, hg]; rfl

theorem IsTw.fst {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a : WDRep h W} {b1 : WDRep h V} {b2 : WDRep h V2} {g : W →ₗ[ℂ] V × V2}
    (hg : IsTw a (b1.sum b2) g) : IsTw a b1 (LinearMap.fst ℂ V V2 ∘ₗ g) := by
  intro σ v
  rw [LinearMap.comp_apply, hg]; rfl

theorem IsTw.snd {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a : WDRep h W} {b1 : WDRep h V} {b2 : WDRep h V2} {g : W →ₗ[ℂ] V × V2}
    (hg : IsTw a (b1.sum b2) g) : IsTw a b2 (LinearMap.snd ℂ V V2 ∘ₗ g) := by
  intro σ v
  rw [LinearMap.comp_apply, hg]; rfl

end

end GlobalTheory.WeilDeligne.NoTwHom
