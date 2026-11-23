import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.Gal.InertialTypesAlt.G

def TwOf {G : Type} [Group G] [TopologicalSpace G] (χ : G → ℂ) (τ τ₁ : SmIrr G) (e : τ.V ≃ₗ[ℂ] τ₁.V) : Prop :=
  ∀ g x, e (χ g • τ.ρ g x) = τ₁.ρ g (e x)

def chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) (g : Gw n v) : ℂ :=
  ((χ.loc v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

def TrTw : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] (m : Measure G) (χ : G → ℂ) (τ τ₁ : SmIrr G) (e : τ.V ≃ₗ[ℂ] τ₁.V), TwOf χ τ τ₁ e → ∀ (f : G → ℂ) (z : ℂ),
    (HasTrace m τ.ρ (fun g => f g * χ g) z ↔ HasTrace m τ₁.ρ f z) ∧
      ∀ I : τ.V ≃ₗ[ℂ] τ.V, HasTwTrace m τ I (fun g => f g * χ g) z ↔ HasTwTrace m τ₁ (e.symm.trans (I.trans e)) f z

def TrBasic : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] (m : Measure G) (τ : SmIrr G) (I : τ.V ≃ₗ[ℂ] τ.V) (f : G → ℂ),
    (∀ z, HasTrace m τ.ρ f z → ∃ t, HasTwTrace m τ I f t) ∧ (∀ t t', HasTwTrace m τ I f t → HasTwTrace m τ I f t' → t = t') ∧
      ∀ d : ENNReal, d ≠ ⊤ → (∀ z, HasTrace m τ.ρ f z → HasTrace (d • m) τ.ρ f ((d.toReal : ℂ) * z)) ∧
        ∀ t, HasTwTrace m τ I f t → HasTwTrace (d • m) τ I f ((d.toReal : ℂ) * t)

def LocTw : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n → ∀ (π : CuspSub K n) (χ : HChar K) (v : Pl K)
    (τ : SmIrr (Gw n v)), (Cusp.cx π).locComp v τ → (∃ τ₁, (Cusp.cx (π.twist χ)).locComp v τ₁) ∧
      ∀ τ₁, (Cusp.cx (π.twist χ)).locComp v τ₁ → ∃ e : τ.V ≃ₗ[ℂ] τ₁.V, TwOf (chiAt n χ v) τ τ₁ e

def ChiBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K), IsLocallyConstant (chiAt n χ v) ∧
    (∀ g, chiAt n χ v g * chiAt n χ⁻¹ v g = 1) ∧ ∀ f : Gw n v → ℂ, Test f → Test fun g => f g * chiAt n χ v g

def LevEx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (f : G → ℂ), IsOpen (K : Set G) →
    (∀ N ∈ nhds (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ N) → Test f →
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ U ≤ K ∧ ∀ u ∈ U, ∀ g, f (u * g) = f g

def CmpIso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (w : PlacesOver E v),
    (∀ u : PlacesOver E v, u = w) → (∃ e : GL (Fin n) (CompletionsOver E v) ≃ₜ* Gw n w.1, ∀ g, e g = GM.cmp w g) ∧
      (∀ g, g ∈ unitSet E n v ↔ GM.cmp w g ∈ GLnLocal.integralGL (w.1.adicCompletion E) n) ∧
      ∀ h : ∀ u : PlacesOver E v, Gw n u.1 → ℂ, GM.prodFn h = fun g => h w (GM.cmp w g)

def NormTriv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (η : HChar F), IsNormChar E η →
    ∀ x, η.1 (GroundTheory.Global.ideleNorm F E x) = 1

def NormLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (v : Pl F) (γ : Gw n v) (δ : GL (Fin n) (CompletionsOver E v)),
      PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) γ → γ ∈ normSet E n v

def NormOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, IsClopen (normSet E n v) ∧ ∀ γ x : Gw n v, x⁻¹ * γ * x ∈ normSet E n v ↔ γ ∈ normSet E n v

def MatchPow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (z : ℂ) (χ : HChar F) (χ' : HChar E), T.IsPow χ z → T.IsPow χ' z → ∀ (v : Pl F) (w : PlacesOver E v), (∀ u : PlacesOver E v, u = w) →
      (∀ s : Gw n w.1 →* Gw n w.1, IsLocGal σ w s → ∀ g, chiAt n χ' w.1 (s g) = chiAt n χ' w.1 g) ∧
      ∀ (c : ℂ) (φ : Gw n w.1 → ℂ) (f : Gw n v → ℂ), GM.MatchAt σ v c (fun g => φ (GM.cmp w g)) f →
        GM.MatchAt σ v c (fun g => φ (GM.cmp w g) * chiAt n χ' w.1 (GM.cmp w g)) fun g => f g * chiAt n χ v g

def WeakPow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (z : ℂ) (χ : HChar F) (χ' : HChar E), T.IsPow χ z → T.IsPow χ' z → ∀ (π : CuspSub F n) (P : CuspSub E n),
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → WeakBC (Cusp.cx (π.twist χ)).sat (Cusp.cx (P.twist χ')).sat

def FibTrace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure]
      (π : CuspSub F n) (P : CuspSub E n) (V : Submodule ℂ (LL μE)) Λ t, Dp.Carries μE P V → T.AtAE μE V Λ t →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (V₀ : Submodule ℂ (LL μF)) Λ₀ t₀, IsSummand μF V₀ → T.AtAE μF V₀ Λ₀ t₀ →
      Λ = bcInf Λ₀ → (∀ᶠ u in cofinite, t u = bcSat t₀ u) →
      ∀ (v : Pl F) [MeasurableSpace (Gw n v)] (m : Measure (Gw n v)) (τ τ₀ : SmIrr (Gw n v)), (Cusp.cx π).locComp v τ →
        Occurs μF V₀ v τ₀ → ∀ (f : Gw n v → ℂ) (z : ℂ), (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace m τ.ρ f z → HasTrace m τ₀.ρ f z

def BaseTw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V →
    ∀ (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀) (v : Pl F), (∀ u : PlacesOver E v, u = T.mk' v) →
      RankOne μ V (T.mk' v).1 (T.J _) (T.χ _) → V ⊓ eigL μ (T.mk' v).1 (T.J _) (T.χ _) ≠ ⊥ →
      ∀ [MeasurableSpace (Gw n (T.mk' v).1)] [BorelSpace (Gw n (T.mk' v).1)] (m : Measure (Gw n (T.mk' v).1)), m.IsHaarMeasure →
      ∀ (τ : SmIrr (Gw n (T.mk' v).1)) (s : Gw n (T.mk' v).1 →* Gw n (T.mk' v).1) (I : τ.V ≃ₗ[ℂ] τ.V), Occurs μ V (T.mk' v).1 τ →
        IsLocGal σ (T.mk' v) s → (∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)) →
        Test ((T.J (T.mk' v).1 : Set (Gw n (T.mk' v).1)).indicator fun x => conj (T.χ (T.mk' v).1 x)) ∧
        ∃ t : ℂ, t ≠ 0 ∧ HasTwTrace m τ I ((T.J (T.mk' v).1 : Set (Gw n (T.mk' v).1)).indicator fun x => conj (T.χ (T.mk' v).1 x)) t

def TrEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n → ∀ (π : CuspSub K n) (v : Pl K)
    [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] (m : Measure (Gw n v)), m.IsHaarMeasure → ∀ τ : SmIrr (Gw n v),
    (Cusp.cx π).locComp v τ → ∀ f : Gw n v → ℂ, Test f → ∃ z, HasTrace m τ.ρ f z

def PowNe : Prop := ∀ Z : Multiset ℂ, Z ≠ 0 → 0 ∉ Z → ∃ᶠ j : ℕ in atTop, (Z.map (· ^ j)).sum ≠ 0

def Core : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (π : CuspSub F n) (P : CuspSub E n) (V : Submodule ℂ (LL μE)),
      Dp.Carries μE P V → (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v →
    ∀ [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] [MeasurableSpace (Gw n w.1)] [BorelSpace (Gw n w.1)]
      (mF : Measure (Gw n v)) (mE : Measure (Gw n w.1)), mF.IsHaarMeasure → mE.IsHaarMeasure →
    ∀ (τ : SmIrr (Gw n v)) (τ' : SmIrr (Gw n w.1)), (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' →
    ∀ (s : Gw n w.1 →* Gw n w.1) (I : τ'.V ≃ₗ[ℂ] τ'.V), IsLocGal σ w s → (∀ g x, I (τ'.ρ g x) = τ'.ρ (s g) (I x)) →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ (φ : Gw n w.1 → ℂ) (f : Gw n v → ℂ) (c₁ z : ℂ), Test φ → Test f →
        GM.MatchAt σ v c₁ (fun g => φ (GM.cmp w g)) f → (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace mF τ.ρ f z →
        HasTwTrace mE τ' I φ (c * c₁ * z)

end UpperTheory.Gal.InertialTypesAlt.G
