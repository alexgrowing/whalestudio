import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Published

def DescentUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
        (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → IsUnramU σ w) ∧
        (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
        ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)

def TypesNZero : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (x : WD h), x.lpDim = n → x.mono0 →
      ∃ (d : ℕ) (ξ : Representation ℂ ↥(GlobalTheory.LFun.KGL w n) (Fin d → ℂ)), ξ.IsIrreducible ∧ GlobalTheory.PRep.IsSmooth ξ ∧
        ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
          ((∃ f : (Fin d → ℂ) →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π.ρ k (f v)) ↔
            ((rc (IrrGL.of π.ρ π.smooth π.irred)).mono0 ∧ ∀ s : ↥(Ine (F := E) A),
              (rc (IrrGL.of π.ρ π.smooth π.irred)).charPol (ineIncl h s) = x.charPol (ineIncl h s))) ∧
          ∀ f f' : (Fin d → ℂ) →ₗ[ℂ] π.V, f ≠ 0 → (∀ k v, f (ξ k v) = π.ρ k (f v)) → (∀ k v, f' (ξ k v) = π.ρ k (f' v)) →
            ∃ c : ℂ, f' = c • f

def SignCsd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutCsd ι r →
    ∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P : GL (Fin n) (Qbar l),
      (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∧ IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P

def CyclicBaseChange : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → (IsTotallyReal K ∨ IsTotallyComplex K) → (IsTotallyReal M ∨ IsTotallyComplex M) →
    ∀ n : ℕ, 1 ≤ n →
      (∀ sat inf, IsCusp (F := K) n sat inf → (∃ η : HChar K, IsNormChar M η ∧ SelfTw sat η) ∨
        ∃ sat' inf', IsCusp (F := M) n sat' inf' ∧ WeakBC sat sat' ∧ ∀ τ m, inf (τ.comp (algebraMap K M)) m → inf' τ m) ∧
      (∀ sat' inf', IsCusp (F := M) n sat' inf' →
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
          ∃ B, sat' w B ∧ sat' w' B) →
        ∃ sat inf, IsCusp (F := K) n sat inf ∧ WeakBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap K M)) m) ∧
      ∀ sat inf sat' inf', IsCusp (F := K) n sat inf → IsCusp (F := M) n sat' inf' → WeakBC sat sat' →
        (∀ η : HChar K, IsNormChar M η → ¬ SelfTw sat η) ∧
        ∀ sat₁ inf₁, IsCusp (F := K) n sat₁ inf₁ → WeakBC sat₁ sat' → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ sat₁ v (B.map (· * η.val v))

def JacquetLanglands : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (lam : InfinitePlace F → DomWeight 2)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (InfinitePlace F → GL (Fin 2) ℂ) V), IsOuter lam ρ →
    ∀ τ : SmIrr (GL (Fin 2) (Af F)),
      ((Q.Occurs ρ τ ∧ ((∃ v, (lam v).w 0 ≠ (lam v).w 1) ∨ ¬ FiniteDimensional ℂ τ.V)) ↔
        ∃ π : TR.CuspSub F 2, π.IsFinComp τ ∧ ∀ v, π.HasInfChar v ((infOfWeight (lam v)).map Neg.neg))

def DefQuatExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Even (Module.finrank ℚ F) → Nonempty (DefQuat F)

def FormsFiniteReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (L : Subgroup (GL (Fin a) (Af F))),
    IsOpen (L : Set (GL (Fin a) (Af F))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (TR.Kinf F a) W),
      GlobalTheory.Published.AutFin.IsContRep ρ → ∀ c : InfinitePlace F → ℂ → ℂ,
      FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F a | TR.IsAutForm φ ∧ (∀ k ∈ L, TR.finRep F a k φ = φ) ∧
        (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
        ∀ v u, TR.cap v u φ = c v u • φ})

def CuspSemisimpleReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a), TR.IsCuspForm φ →
    (∃ s : ℂ, TR.lie F a (TR.oneL F a) φ = s • φ) → φ ∈ ⨆ π : TR.CuspSub F a, π.V

def DeRhamCharAlg : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 1) (Qbar l)), Continuous r →
    (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
      ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O) (Bw : LocBridge l F Ω (Dec (F := F) A) O),
        Induces Bw ∧ IsdRAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)) →
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r)

end UpperTheory.V.Published
