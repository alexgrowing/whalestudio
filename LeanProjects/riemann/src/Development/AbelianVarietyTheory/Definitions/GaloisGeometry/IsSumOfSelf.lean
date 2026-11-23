import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

structure Base : Prop where
  llc : GlobalTheory.Published.LocalLanglandsGL
  ex : GlobalTheory.Published.LocalLanglandsExists
  conv : GlobalTheory.Published.LocalConverseGL
  adm : GlobalTheory.Published.IrreducibleAdmissibleGL
  len : GlobalTheory.Published.StandardFunctorsFiniteLength
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  js : GlobalTheory.Published.JacquetShalikaRigidity
  gk : GlobalTheory.Published.GelfandKazhdanDual

theorem Base.uniq (H : Base) : GlobalTheory.TheRec.RecUnique :=
  GlobalTheory.TheRec.recUnique_of_localConverse H.ex H.conv H.exh H.adm H.len

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SatMatch (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, sat w B ∧
    ∀ (_hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      IsWDOf ι r ((WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2))

theorem SatMatch.wdOf_eq {sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} (H : SatMatch sat ι r) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, sat w B ∧
      ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        wdOf h hl ι r = (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2) :=
  H.mono fun _ ⟨B, hB, hw⟩ => ⟨B, hB, fun hl A h => (hw hl A h).wdOf_eq hl⟩

def IsSumOf {Γ k : Type} [Group Γ] [Field k] {a m : ℕ} {b : Fin m → ℕ} (r : Γ →* GL (Fin a) k)
    (ρ : ∀ i, Γ →* GL (Fin (b i)) k) : Prop :=
  ∀ g, (r g).val.trace = ∑ i, (ρ i g).val.trace

def GalPol [IsCMField E] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∃ (χ : HChar (maximalRealSubfield E)) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
    (∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a) ∧ IsLAdicCharOf ι χ μ ∧
    ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
      IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

example {Γ k : Type} [Group Γ] [Field k] {a : ℕ} {b : Fin 2 → ℕ} (r : Γ →* GL (Fin a) k)
    (ρ : ∀ i, Γ →* GL (Fin (b i)) k) (H : IsSumOf r ρ) (g : Γ) :
    (r g).val.trace = (ρ 0 g).val.trace + (ρ 1 g).val.trace := by
  have := H g; rwa [Fin.sum_univ_two] at this

example (H : Base) : GlobalTheory.TheRec.RecUnique := H.uniq

end GlobalTheory.AboveL

end
