import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T

section Defs

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def AtAE (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) : Prop := ∃ S : Set (Pl K), S.Finite ∧ At μ S V Λ t

def IsPow (χ : HChar K) (s : ℂ) : Prop :=
  ∀ x, ((χ.1 x : ℂˣ) : ℂ) = (((GroundTheory.Global.IdeleGroup.ideleModule K x).1 : ℝ) : ℂ) ^ s

def Parts [IsTotallyComplex K] (t : Pl K → Multiset ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (P : ∀ i, CG K (m i)), (∀ i, 1 ≤ m i) ∧ 2 ≤ Fintype.card ι ∧
    ∀ᶠ w in cofinite, ∃ B, R.sumSat P w B ∧ t w = B.map fun b : ℂˣ => (b : ℂ)

variable (F : Type) [Field F] [NumberField F] [Algebra F K]

def OffAll (n : ℕ) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) : Prop :=
  ∀ S : Set (Pl F), S.Finite → OffFam F n {w : Pl K | w.under (𝓞 F) ∈ S} S Λ t

variable (K) in

def LiftPlus [IsTotallyComplex F] [IsTotallyComplex K] (n : ℕ) : Prop :=
  ∀ π : CG F n, ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (P : ∀ i, CG K (m i)), (∀ i, 1 ≤ m i) ∧ Nonempty ι ∧
    WeakBC π.HasSat (R.sumSat P)

variable {F}

def LocIso {v : Pl F} (w : PlacesOver K v) (τ : SmIrr (Gw n v)) (τ' : SmIrr (Gw n w.1)) : Prop :=
  ∃ e : τ.V ≃ₗ[ℂ] τ'.V, ∀ g x, e (τ.ρ g x) = τ'.ρ (mapGL n (completionMap v w.1) g) (e x)

def IsLift (π : Cusp F n) (P : Cusp K n) : Prop :=
  WeakBC π.sat P.sat ∧ ∀ τ m, π.inf (τ.comp (algebraMap F K)) m ↔ P.inf τ m

end Defs

def Places : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (Module.finrank F E).Prime →
    {v : Pl F | GM.Split E v}.Infinite ∧ (∀ᶠ v : Pl F in cofinite, GM.Unr E v) ∧ (∀ v : Pl F, Nonempty (PlacesOver E v)) ∧
    (∀ v : Pl F, ¬ GM.Split E v → ∀ w w' : PlacesOver E v, w' = w) ∧
    (∀ w : Pl E, Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ resDeg F w) ∧
    ∀ (v : Pl F) (w : Pl E) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
      (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
      GM.Split E v ∧ ∃ u : PlacesOver E v, ∃ h : u.1 = w, ∀ x, i x = h ▸ completionMap v u.1 x

def MatchOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : Pl F)
    [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
    [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))],
    ∃ (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure ∧ mF.IsHaarMeasure ∧ mE (unitSet E n v) = 1 ∧ mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 ∧
      ∀ c φ f, Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF c φ f → GM.MatchAt σ v c φ f

def LocUp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)), q ∉ S → (∀ v ∉ S, GM.Unr E v) →
    ∀ U₀ : ∀ v : Pl F, Subgroup (Gw n v), (∀ v, IsOpen (U₀ v : Set (Gw n v))) →
    ∃ L : GM.Loc σ n q w₀, L.S = S ∧ ∀ v ∈ S, L.c v ≠ 0 ∧ L.UF v ≤ U₀ v ∧ L.f v = (L.UF v : Set (Gw n v)).indicator 1

def AmpFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ),
    (∀ x : ℝ, 0 < x → {V | IsSummand μ V ∧ eigIn V 𝔞.A x ≠ ⊥}.Finite) ∧
      ∀ V, IsSummand μ V → (∃ v ∈ V, 𝔞.A v ≠ 0) → ∃ x : ℝ, 0 < x ∧ eigIn V 𝔞.A x ≠ ⊥

def LevelEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ S : Finset (Pl K), (∀ w ∉ S, V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) ≠ ⊥) →
    ∃ U : ∀ w : Pl K, Subgroup (Gw n w), (∀ w, CO (U w) ∧ U w ≤ GLnLocal.integralGL (w.adicCompletion K) n) ∧
      V ⊓ sphOff μ S ⊓ ⨅ w ∈ S, fixL μ w (U w) ≠ ⊥

def PosSide : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL F n)) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q) (ν : Measure (archGroup F n))
      [ν.IsHaarMeasure] (a : TI F n) (L : GM.Loc σ n q w₀) (e : Fin n → ℤ) (l : ℕ) (𝔣 : Side (Twist.id μ) l), Antitone e →
      GM.IsSideF L ν a e 𝔣 → (∀ v ∈ L.S, L.f v = (L.UF v : Set (Gw n v)).indicator 1) →
      ∀ (p : Submodule ℂ (LL μ) → Prop) (V : Submodule ℂ (LL μ)) (x : ℝ), IsSummand μ V → p V → 0 < x →
        eigIn V 𝔣.toAmp.A x ≠ ⊥ → ∃ᶠ j in atTop, 𝔣.tr p x j ≠ 0

def GoodEx : Prop := ∀ n : ℕ, 0 < n → ∃ ν : Fin n → ℤ, GM.Good ν

def CoreLift : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE),
      IsGalTwist σ θ → ∀ (V : Submodule ℂ (LL μF)) Λ t, IsSummand μF V → AtAE μF V Λ t → OffAll F n (bcInf (K := E) Λ) (bcSat t) →
      ∃ V' : Submodule ℂ (LL μE), IsSummand μE V' ∧ V'.map (θ.U : LL μE →ₗ[ℂ] LL μE) = V' ∧ AtAE μE V' (bcInf Λ) (bcSat t)

def HoweType : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V →
    ∀ (v : Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) → ∀ N ∈ nhds (1 : Gw n w.1),
      ∃ (J : Subgroup (Gw n w.1)) (χ : Gw n w.1 → ℂ), CO J ∧ IsChr J χ ∧ (J : Set (Gw n w.1)) ⊆ N ∧ RankOne μ V w.1 J χ ∧
        V ⊓ eigL μ w.1 J χ ≠ ⊥ ∧ ∀ x : GL (Fin n) (CompletionsOver E v), GM.cmp w x ∈ J →
          GM.cmp w (mapGL n (galFin σ v) x) ∈ J ∧ χ (GM.cmp w (mapGL n (galFin σ v) x)) = χ (GM.cmp w x)

def TyEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ S : Finset (Pl F), q ∉ S → (∀ v ∉ S, GM.Unr E v) →
      (∀ w : Pl E, w.under (𝓞 F) ∉ S → V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥) →
      ∀ mk : ∀ v : Pl F, PlacesOver E v,
      ∃ T : Ty σ n q w₀, T.S = S ∧ T.mk' = mk ∧ V ⊓ T.typed μ ≠ ⊥ ∧
        (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v, RankOne μ V u.1 (T.J u.1) (T.χ u.1)) ∧
        ∃ (c : Pl F → ℂ) (f₀ : ∀ v : Pl F, Gw n v → ℂ) (UF : ∀ v : Pl F, Subgroup (Gw n v)),
          (∀ v ∈ T.sp, ∀ g, g ∈ UF v ↔ mapGL n (completionMap v (T.mk' v).1) g ∈ T.J (T.mk' v).1) ∧
          ∀ ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ,
            (∀ v ∈ T.sp, Test (ψ v) ∧ ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g ∧ ψ v (g * u) = ψ v g) →
            ∃ L : GM.Loc σ n q w₀, T.Fits L ψ ∧ (∀ v ∈ S, L.c v = c v ∧ L.UF v = UF v) ∧
              (∀ v ∈ T.sp, L.f v = fun g => ψ v (mapGL n (completionMap v (T.mk' v).1) g)) ∧
              ∀ v ∈ S, ¬ GM.Split E v → L.f v = f₀ v

def TermE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ m : ℕ, Module.finrank F E = m + 1 → ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v, RankOne μ V u.1 (T.J u.1) (T.χ u.1)) →
      (∃ v ∈ V ⊓ T.typed μ, OComponent μ (s 0) (hs 0) νF a v ≠ 0) →
    ∀ [∀ w : Pl E, MeasurableSpace (Gw n w)] [∀ w : Pl E, BorelSpace (Gw n w)] (mm : ∀ w : Pl E, Measure (Gw n w)),
      (∀ w, (mm w).IsHaarMeasure) → ∀ τ : ∀ w : Pl E, SmIrr (Gw n w), (∀ w, Occurs μ V w (τ w)) → ∀ ν : Fin n → ℤ, Antitone ν →
      ∃ (x : ℝ) (c : ℂ) (Z : Multiset ℂ), 0 < x ∧ c ≠ 0 ∧ Z ≠ 0 ∧ 0 ∉ Z ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
        ∀ (l : ℕ) (𝔢 : Side θ l), GM.IsSideE L νE aE ν 𝔢 → ∀ sv : Pl F → ℂ,
          (∀ v ∈ T.sp, HasTrace (mm (T.mk' v).1) (τ (T.mk' v).1).ρ (ψ v) (sv v)) → ∀ j : ℕ,
          trOn (eigIn V 𝔢.toAmp.A x) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) = c * (Z.map (· ^ j)).sum * ∏ v ∈ T.sp, sv v

def CoreDesc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE),
      IsGalTwist σ θ → ∀ (V : Submodule ℂ (LL μE)) Λ t, IsSummand μE V → V.map (θ.U : LL μE →ₗ[ℂ] LL μE) = V → AtAE μE V Λ t →
      OffAll F n Λ t → ∀ (v : Pl F) (w : PlacesOver E v), GM.Split E v → ∀ τ' : SmIrr (Gw n w.1), Occurs μE V w.1 τ' →
      ∃ (V₀ : Submodule ℂ (LL μF)) (Λ₀ : (F →+* ℂ) → Multiset ℂ) (t₀ : Pl F → Multiset ℂ), IsSummand μF V₀ ∧ AtAE μF V₀ Λ₀ t₀ ∧
        Λ = bcInf Λ₀ ∧ (∀ᶠ u in cofinite, t u = bcSat t₀ u) ∧ ∃ τ, Occurs μF V₀ v τ ∧ LocIso w τ τ'

def FamSat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (b : Datum K n) (S : Set (Pl K)), S.Finite →
    ∀ Λ t, b.Pt S Λ t → ∃ P : ∀ i, CG K (b.d i), ∀ w ∉ S, ∃ B, R.sumSat P w B ∧ t w = B.map fun z : ℂˣ => (z : ℂ)

def FamParts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    (∀ m, 1 ≤ m → m < n → LiftPlus E F m) → ∀ (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ), ¬ OffAll F n Λ t → Parts t

def PowTwist : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E],
    (∀ s, (∃ χ : HChar F, IsPow χ s) ∧ ∃ χ : HChar E, IsPow χ s) ∧
    ∀ (s : ℂ) (χ : HChar F) (χ' : HChar E), IsPow χ s → IsPow χ' s → IsPow χ⁻¹ (-s) ∧ IsPow χ'⁻¹ (-s) ∧ ∀ n : ℕ, 1 ≤ n →
      (∀ π : CuspSub F n, (π.twist χ).twist χ⁻¹ = π) ∧ (∀ P : CuspSub E n, (P.twist χ').twist χ'⁻¹ = P) ∧
      (∀ (π : CuspSub F n) (P : CuspSub E n), IsLift (.cx π) (.cx P) → IsLift (.cx (π.twist χ)) (.cx (P.twist χ'))) ∧
      (∀ (P : CuspSub E n) (g : E ≃+* E), (Cusp.cx P).ConjIso g → (Cusp.cx (P.twist χ')).ConjIso g) ∧
      ∀ (π : CuspSub F n) (P : CuspSub E n) (v : Pl F) (w : PlacesOver E v), Function.Surjective (completionMap v w.1) →
        (∀ τ τ', (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' → LocIso w τ τ') →
        ∀ τ τ', (Cusp.cx (π.twist χ)).locComp v τ → (Cusp.cx (P.twist χ')).locComp w.1 τ' → LocIso w τ τ'

def CarryLift : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure],
    (∀ V, IsSummand μF V → ∃ Λ t, AtAE μF V Λ t) ∧ (∀ V, IsSummand μE V → ∃ Λ t, AtAE μE V Λ t) ∧
    (∀ (π : CuspSub F n) (P : CuspSub E n) V V' Λ t Λ' t', Dp.Carries μF π V → Dp.Carries μE P V' → AtAE μF V Λ t →
      AtAE μE V' Λ' t' → Λ' = bcInf Λ → (∀ᶠ u in cofinite, t' u = bcSat t u) → IsLift (.cx π) (.cx P)) ∧
    (∀ (π : CuspSub F n) V Λ t, Dp.Carries μF π V → AtAE μF V Λ t → Parts (bcSat (K := E) t) →
      ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (Q : ∀ i, CG E (m i)), (∀ i, 1 ≤ m i) ∧ 2 ≤ Fintype.card ι ∧
        WeakBC (CG.mk π).HasSat (R.sumSat Q)) ∧
    (∀ (P : CuspSub E n) V Λ t, Dp.Carries μE P V → AtAE μE V Λ t → ¬ Parts t) ∧
    ∃ θ : Twist μE, IsGalTwist σ θ ∧ ∀ (P : CuspSub E n) V, Dp.Carries μE P V →
      ((∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) ↔ V.map (θ.U : LL μE →ₗ[ℂ] LL μE) = V)

def LiftStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    (∀ m, 1 ≤ m → m < n → LiftPlus E F m) → ∀ π : CuspSub F n,
      (∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (Q : ∀ i, CG E (m i)), (∀ i, 1 ≤ m i) ∧ 2 ≤ Fintype.card ι ∧
        WeakBC (CG.mk π).HasSat (R.sumSat Q)) ∨
      ∃ P : CuspSub E n, IsLift (.cx π) (.cx P) ∧ ∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv

def LiftAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n → LiftPlus E F n

def DescStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ P : CuspSub E n, (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) → ∀ (v : Pl F) (w : PlacesOver E v), GM.Split E v →
      ∃ π : CuspSub F n, IsLift (.cx π) (.cx P) ∧ ∀ τ τ', (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' → LocIso w τ τ'

def NormCharSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ η : HChar F, IsNormChar E η → ∀ v : Pl F, GM.Split E v → ∀ (π : CuspSub F n) τ,
      (Cusp.cx (π.twist η)).locComp v τ ↔ (Cusp.cx π).locComp v τ

def SplitStrong : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → SplitLift (Cusp.cx π) (Cusp.cx P)

end UpperTheory.ConvolutionTheory.T
