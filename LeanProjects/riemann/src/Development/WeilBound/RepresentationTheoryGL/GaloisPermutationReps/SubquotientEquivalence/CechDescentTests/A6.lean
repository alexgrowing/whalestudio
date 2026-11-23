import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsLevelOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.SeparatingWords.ExpDefs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing Ysupp.Exp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzT

def A1 : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (m : ℕ),
  (prinSeries fun _ : Fin m => unrChar (w.adicCompletion E) 1).IsIrreducible ∧
    ∃ hd : ∑ j : Fin m, ((fun _ : Fin m => zc (w.adicCompletion E) 1) j).1 = m,
      Nonempty ((prinSeries fun _ : Fin m => unrChar (w.adicCompletion E) 1).Equiv
        (prodIrr (fun _ : Fin m => zc (w.adicCompletion E) 1) hd))

def A2 : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ)
  (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h),
  LawsLit a ha e rc → ∀ (m : ℕ) (τ : IrrRep (GL (Fin m) (w.adicCompletion E)))
    (hd : ∑ j : Fin m, ((fun _ : Fin m => zc (w.adicCompletion E) 1) j).1 = m),
    Nonempty (τ.ρ.Equiv (prodIrr (fun _ : Fin m => zc (w.adicCompletion E) 1) hd)) →
    ∃ L : List {μ : (w.adicCompletion E)ˣ →* ℂˣ // IsUnram μ}, L.length = m ∧ rc (cls τ) = sumList (L.map (unrPar a ha))

def A3 : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin m) k) V) (hd : ∑ j : Fin m, ((fun _ : Fin m => zc k 1) j).1 = m),
    Nonempty (ρ.Equiv (prodIrr (fun _ : Fin m => zc k 1) hd)) → GlobalTheory.Whittaker.IsGeneric ψ ρ

def A4 : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (m : ℕ) (V : Type) [AddCommGroup V]
  [Module ℂ V] (ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V) (α : Fin m → ℂˣ), ρ.IsIrreducible →
    GlobalTheory.LFun.HasSatGL w ρ (Finset.univ.val.map α) → ∀ ψ : AddChar (w.adicCompletion E) Circle, HasConductor ψ 1 →
    ∀ l : Module.Dual ℂ V, l ≠ 0 → GlobalTheory.Whittaker.IsFunctional ψ ρ l →
      ∃ v ∈ fixed ρ (KO (w.adicCompletion E) (Fin m)), l v ≠ 0

def A5 : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ψ' ψ : AddChar k Circle) (c : kˣ), ord k c = 1 → (∀ x, ψ x = ψ' ((c : k) * x)) → HasConductor ψ 1 →
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin m) k) V), IsSmooth ρ →
    ∀ l : Module.Dual ℂ V, GlobalTheory.Whittaker.IsFunctional ψ ρ l → ∀ v ∈ fixed ρ (KO k (Fin m)), l v ≠ 0 →
      ∃ v' ∈ fixed ρ (KOne k (Fin m)), ∃ l' : Module.Dual ℂ V, GlobalTheory.Whittaker.IsFunctional ψ' ρ l' ∧ l' v' ≠ 0

def A6 : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
  (∀ ψ' : AddChar k Circle, Continuous ψ' → IsLevelOne ψ' → ∃ (ψ : AddChar k Circle) (c : kˣ), ord k c = 1 ∧
    (∀ x, ψ x = ψ' ((c : k) * x)) ∧ HasConductor ψ 1 ∧ Continuous ψ ∧ ψ ≠ 1) ∧
  ∀ (m : ℕ) (τ : IrrRep (GL (Fin m) k)), ∃ ω : kˣ →* ℂˣ, HasCentralChar τ.ρ ω

end PositivityTheory.Rg.DzT

end
