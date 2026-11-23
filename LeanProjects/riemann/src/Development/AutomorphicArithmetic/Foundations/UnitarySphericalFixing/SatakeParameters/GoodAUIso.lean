import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain
open UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def GoodAU (π : NG.AutRep L n) : Prop := ∀ (s : SplitPlace L) σ, IsLocS π.S s σ → Good (GlobalTheory.LocLanglands.cls σ)

def NoSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop :=
  ∀ s : SplitPlace L, s.v ≠ v

def SphAtG (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop :=
  π.SphAt v ∧ (NoSplit L v → GoodAU π)

theorem goodAU_iso {π π' : NG.AutRep L n} (h : π.Iso π') (hg : GoodAU π) : GoodAU π' := fun s σ' hσ' => by
  obtain ⟨x, σ₀, σ, e, hσ, hx⟩ := GlobalTheory.AutQuot.locAt_of_split π s
  have h1 : x = GlobalTheory.LocLanglands.cls σ' := GlobalTheory.AutQuot.locAt_unique h ⟨σ₀, σ, e, hσ, hx⟩ ⟨s, σ', rfl, hσ', HEq.rfl⟩
  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (e : σ₀.w = w) (y : GlobalTheory.LocGL.IrrGL (w.adicCompletion L)),
      HEq (GlobalTheory.LocLanglands.cls σ) y → Good y := by
    rintro _ rfl y hy
    exact eq_of_heq hy ▸ hg σ₀ σ hσ
  exact h1 ▸ key _ e x hx

namespace Old

def Sph0 (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop := π.SphAt v

theorem sphGood (s : Sw) {π : NG.AutRep L n} {v} (_h : π.SphAt v) : NoSplit L v → GoodAU π := s.elim

theorem sphMk {π : NG.AutRep L n} {v} (h : Sph0 π v) (_hg : NoSplit L v → GoodAU π) : π.SphAt v := h

end Old

namespace New

def Sph0 (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Prop := π.SphAt v

theorem sphGood (_ : TrivialCondition) {π : NG.AutRep L n} {v} (h : SphAtG π v) : NoSplit L v → GoodAU π := h.2

theorem sphMk {π : NG.AutRep L n} {v} (h : Sph0 π v) (hg : NoSplit L v → GoodAU π) : SphAtG π v := ⟨h, hg⟩

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : SphAtG π v) : SphAtG π' v :=
  ⟨GlobalTheory.AutQuot.sphAt_iso h hs.1, fun hv => goodAU_iso h (hs.2 hv)⟩

end New

end UpperTheory.One.M

end
