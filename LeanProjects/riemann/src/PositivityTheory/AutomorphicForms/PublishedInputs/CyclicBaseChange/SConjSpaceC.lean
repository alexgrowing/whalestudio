import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.IsGalAd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

def SCuspOf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) sat inf, IsCusp (F := F) n sat inf → ∃ π : Cusp F n, π.sat = sat ∧ π.inf = inf

def SIsCusp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n), IsCusp (F := F) n π.sat π.inf

def SIsoSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π π' : Cusp F n), π.Iso π' → ∀ w B, π.sat w B → π'.sat w B

def STwSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n) (η : HChar F),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ ∀ B, π.sat v B → (π.twist η).sat v (B.map (· * η.val v))

def SSatEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.sat v B

def SSatUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n) v B B', π.sat v B → π.sat v B' → B = B'

def SSmo : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → StrongMultOneReal → ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 1 ≤ n → ∀ π π' : Cusp F n,
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.sat w B ∧ π'.sat w B) → π.Iso π'

def SConjSpaceC : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsTotallyComplex M] (σ : M ≃+* M) (s : Ad M ≃+* Ad M), IsGalAd σ s →
    ∀ (n : ℕ) (P : CuspSub M n), ∃ P' : CuspSub M n,
      (Cusp.cx P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space

def SConjSpaceR : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsTotallyReal M] (σ : M ≃+* M) (s : Ad M ≃+* Ad M), IsGalAd σ s →
    ∀ (n : ℕ) (P : UpperTheory.V.TR.CuspSub M n), ∃ P' : UpperTheory.V.TR.CuspSub M n,
      (Cusp.re P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space

def SConjSatC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsTotallyComplex M] (σ : M ≃ₐ[K] M)
    (s : Ad M ≃+* Ad M), IsGalAd σ.toRingEquiv s → ∀ (n : ℕ) (P P' : CuspSub M n),
    (Cusp.cx P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space →
    ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
      (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, (CG.mk P).HasSat (g w) B → (CG.mk P').HasSat w B

def SConjSatR : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsTotallyReal M] (σ : M ≃ₐ[K] M)
    (s : Ad M ≃+* Ad M), IsGalAd σ.toRingEquiv s → ∀ (n : ℕ) (P P' : UpperTheory.V.TR.CuspSub M n),
    (Cusp.re P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space →
    ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
      (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.HasSat (g w) B → P'.HasSat w B

def SNormPow : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f

end UpperTheory.CBC
