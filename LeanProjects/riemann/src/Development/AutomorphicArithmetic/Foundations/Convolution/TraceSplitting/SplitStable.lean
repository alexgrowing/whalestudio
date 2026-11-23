import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

def AbsLast : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K) [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)]
    (m : Measure (Gw n v)) [m.IsHaarMeasure] (U : Subgroup (Gw n v)), CO U →
    ∀ (ι : Type) [Fintype ι] (τ : ι → SmIrr (Gw n v)) (a : ι → ℂ) (Z : ι → Multiset ℂ) (τ₀ : SmIrr (Gw n v)) (c : ℂ) (Z₀ : Multiset ℂ),
    c ≠ 0 → Z₀ ≠ 0 → 0 ∉ Z₀ → (∀ i, 0 ∉ Z i) → fixedVectors τ₀.ρ U ≠ ⊥ →
    (∀ (φ : Gw n v → ℂ) (s₀ : ℂ) (s : ι → ℂ), Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
      HasTrace m τ₀.ρ φ s₀ → (∀ i, HasTrace m (τ i).ρ φ (s i)) →
      ∀ᶠ j : ℕ in atTop, c * (Z₀.map (· ^ j)).sum * s₀ = ∑ i, a i * ((Z i).map (· ^ j)).sum * s i) →
    ∃ i, Nonempty ((τ i).ρ.Equiv τ₀.ρ)

def PullBack : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) →
    ∀ [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] [MeasurableSpace (Gw n w.1)] [BorelSpace (Gw n w.1)]
      (mF : Measure (Gw n v)) (mE : Measure (Gw n w.1)), mF.IsHaarMeasure → mE.IsHaarMeasure → ∀ τ' : SmIrr (Gw n w.1),
    ∃ (τ : SmIrr (Gw n v)) (r : ℂ), r ≠ 0 ∧ (∀ τ₁ : SmIrr (Gw n v), Nonempty (τ₁.ρ.Equiv τ.ρ) → LocIso w τ₁ τ') ∧
      (∀ (ψ : Gw n w.1 → ℂ) (s : ℂ), HasTrace mF τ.ρ (fun g => ψ (mapGL n (completionMap v w.1) g)) s → HasTrace mE τ'.ρ ψ (r * s)) ∧
      ∀ (J : Subgroup (Gw n w.1)) (U : Subgroup (Gw n v)), CO J → (∀ g, g ∈ U ↔ mapGL n (completionMap v w.1) g ∈ J) →
        CO U ∧ (fixedVectors τ'.ρ J ≠ ⊥ → fixedVectors τ.ρ U ≠ ⊥) ∧
        ∀ φ : Gw n v → ℂ, Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
          ∃ ψ : Gw n w.1 → ℂ, Test ψ ∧ (∀ u ∈ J, ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) ∧
            φ = fun g => ψ (mapGL n (completionMap v w.1) g)

def UnitTrace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)), m.IsHaarMeasure →
    ∀ (τ : SmIrr (Gw n w)) (J : Subgroup (Gw n w)), Occurs μ V w τ → CO J → V ⊓ fixL μ w J ≠ ⊥ →
      fixedVectors τ.ρ J ≠ ⊥ ∧ Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) ∧
      (∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
        (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g) ∧
      ∃ s : ℂ, s ≠ 0 ∧ HasTrace m τ.ρ ((J : Set (Gw n w)).indicator 1) s

def OneTerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n l : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (V : Submodule ℂ (LL μ)) Λ t,
    IsSummand μ V → V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V → At μ 𝔰.S V Λ t → ∀ (x : ℝ) (j : ℕ),
      𝔰.tr (fun V' => At μ 𝔰.S V' Λ t) x j = trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)

def SideSum : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL F n)) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (UF : ∀ v : Pl F, Subgroup (Gw n v)) (e : Fin n → ℤ),
      Antitone e → ∀ (p : Submodule ℂ (LL μ) → Prop) (x : ℝ), 0 < x →
      ∃ (ι : Type) (_ : Fintype ι) (V : ι → Submodule ℂ (LL μ)) (τ : ι → ∀ v : Pl F, SmIrr (Gw n v)) (b : ι → ℂ) (Z : ι → Multiset ℂ),
        (∀ i, IsSummand μ (V i) ∧ p (V i) ∧ 0 ∉ Z i ∧ ∀ v, Occurs μ (V i) v (τ i v)) ∧
        ∀ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S → (∀ v ∈ S, L.UF v = UF v) → GM.IsSideF L ν a e 𝔣 →
          ∀ s : ι → Pl F → ℂ, (∀ i, ∀ v ∈ S, HasTrace (m v) (τ i v).ρ (L.f v) (s i v)) → ∀ j : ℕ,
            𝔣.tr p x j = ∑ i, b i * ((Z i).map (· ^ j)).sum * ∏ v ∈ S, s i v

def PickS : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) Λ t, IsSummand μ V → AtAE μ V Λ t → ∀ v : Pl F,
      ∃ (S : Finset (Pl F)) (q : Pl F) (_ : PlacesOver E q), v ∈ S ∧ q ∉ S ∧ GM.Split E q ∧ (∀ u ∉ S, GM.Unr E u) ∧
        (∀ w : Pl E, w.under (𝓞 F) ∉ S → V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥) ∧
        ∀ S' : Set (Pl E), (∀ w, w ∈ S' ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q) →
          At μ S' V Λ t ∧ (∀ τ, (Λ τ).card = n) ∧ ∀ w ∉ S', (t w).card = n ∧ 0 ∉ t w

def PickInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (u : LL μE), u ≠ 0 →
      ∃ (m : ℕ) (_ : Module.finrank F E = m + 1) (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n)
        (hs : ∀ i, Continuous (s i)) (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (νF : Measure (archGroup F n))
        (_ : νF.IsHaarMeasure) (b a : TI F n) (aE : TI E n) (aF : TI F n), IsBlockElement D n s ∧ ArchSlot D νE νF b a aE aF ∧
        GM.AmpFn μE νE aE ∧ GM.AmpFn μF νF aF ∧ GM.ArchPair σ νE νF aE aF 1 ∧ OComponent μE (s 0) (hs 0) νF a u ≠ 0

def SplitLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v : Pl F, GM.Split E v →
      ∃ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)), CO U ∧
        U ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        ∀ u, CO (J u) ∧ (∀ g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) ∧ V ⊓ fixL μ u.1 (J u) ≠ ⊥

def SplitStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, GM.Split E v → ∀ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)),
      (∀ u g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) →
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
      (CO U → U ≤ GLnLocal.integralGL (v.adicCompletion F) n →
        ∃ UE : Subgroup (GL (Fin n) (CompletionsOver E v)), (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
          IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v)

def SplitMatch : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (v : Pl F) (w : PlacesOver E v), GM.Split E v → ∀ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)),
      CO U → (∀ u, CO (J u) ∧ ∀ g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) →
      ∃ c : ℂ, ∀ ψ : Gw n w.1 → ℂ, Test ψ → (∀ u ∈ J w, ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ))
          (fun g => ψ (mapGL n (completionMap v w.1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v w.1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ) g) ∧
        ∀ y ∈ U, ∀ g, ψ (mapGL n (completionMap v w.1) (y * g)) = ψ (mapGL n (completionMap v w.1) g)

def InertData : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v : Pl F, ¬ GM.Split E v →
      ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ) (f : Gw n v → ℂ)
        (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
        (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ RankOne μ V u.1 (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
        (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
        GM.MatchAt σ v 1 (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f ∧
        IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧
        IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f (y * g) = f g

def OffStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ GLnLocal.integralGL (u.1.adicCompletion E) n) →
        ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ GLnLocal.integralGL (u.1.adicCompletion E) n) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) →
        ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
      (∃ U : Subgroup (GL (Fin n) (CompletionsOver E v)), (U : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v) ∧
      (∃ U : Subgroup (GL (Fin n) (CompletionsOver E v)), ∀ g, g ∈ U ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
      ∀ w : Pl E, CO (GLnLocal.integralGL (w.adicCompletion E) n) ∧ CO (GLnLocal.iwahori (w.adicCompletion E) n) ∧
        GLnLocal.iwahori (w.adicCompletion E) n ≤ GLnLocal.integralGL (w.adicCompletion E) n

end UpperTheory.ConvolutionTheory.T
