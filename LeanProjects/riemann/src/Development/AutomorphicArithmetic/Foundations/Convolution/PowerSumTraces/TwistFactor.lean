import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.L1
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

def HasTwTrace {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (m : Measure G) (τ : SmIrr G)
    (I : τ.V ≃ₗ[ℂ] τ.V) (φ : G → ℂ) (t : ℂ) : Prop :=
  ∃ B : τ.V →ₗ[ℂ] τ.V, IsIntegralOp m τ.ρ φ B ∧ HasFinTrace (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) t

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsLocGal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (s : Gw n w.1 →* Gw n w.1) : Prop :=
  ∀ g : GL (Fin n) (CompletionsOver E v), GM.cmp w (mapGL n (galFin σ v) g) = s (GM.cmp w g)

structure FitsV {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q} (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀)
    (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) : Prop where
  S_eq : L.S = T.S
  test : ∀ v ∈ T.S, Test (ψ v)
  inv : ∀ v ∈ T.sp, ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g ∧ ψ v (g * u) = ψ v g
  split : ∀ v ∈ T.sp, L.φ v = GM.prodFn (Function.update
      (fun u : PlacesOver E v => ((T.J u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (T.mk' v) (ψ v)) ∧
    ∀ g, g ∈ L.UE v ↔ ∀ u, GM.cmp u g ∈ T.J u.1
  nonsplit : ∀ v ∈ T.S, ¬ GM.Split E v → ∀ g, L.φ v g = ψ v (GM.cmp (T.mk' v) g)

end

def TwistFactor : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V Z : Submodule ℂ (LL μ))
    (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
    (τ : ∀ i, SmIrr (Gw n (w i))) (s : ∀ i, Gw n (w i) ≃ₜ* Gw n (w i)) (I : ∀ i, (τ i).V ≃ₗ[ℂ] (τ i).V) (R : LL μ →L[ℂ] LL μ),
    IsSummand μ V → Function.Injective w → (∀ i, Occurs μ V (w i) (τ i)) →
    Z ≤ V → IsClosed (Z : Set (LL μ)) → (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) →
    (∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (U i))) →
    (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (rhoL μ (w i) g v) = rhoL μ (w i) (s i g) (R v)) →
    (∀ i g x, I i ((τ i).ρ g x) = (τ i).ρ (s i g) (I i x)) →
    ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (Gw n (w i))) (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ)
      (T : Fin r → LL μ →L[ℂ] LL μ) (t : Fin r → ℂ), (∀ i, CO (U i)) → (∀ i, (m i).IsHaarMeasure) → (∀ i, Test (φ i)) →
      (∀ i, ∀ u ∈ U i, ∀ g, φ i (u * g) = φ i g) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ i, HasTwTrace (m i) (τ i) (I i) (φ i) (t i)) →
      trOn (Z ⊓ ⨅ i, fixL μ (w i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i

def LocGalEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (Module.finrank F E).Prime → ∀ (n : ℕ) (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v →
    (∀ u : PlacesOver E v, u = w) ∧ ∃ s : Gw n w.1 ≃ₜ* Gw n w.1, IsLocGal σ w (s : Gw n w.1 →* Gw n w.1) ∧
      ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        (∀ g x, θ.U (rhoL μ w.1 g x) = rhoL μ w.1 (s g) (θ.U x)) ∧
        ∀ (V : Submodule ℂ (LL μ)) (τ : SmIrr (Gw n w.1)), IsSummand μ V → V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
          Occurs μ V w.1 τ → ∃ I : τ.V ≃ₗ[ℂ] τ.V, ∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)

def TermEV : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ, Module.finrank F E = k + 1 → (k + 1).Prime → 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (m : ∀ u : Pl E, Measure (Gw n u)),
      (∀ u, (m u).IsHaarMeasure) →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v,
        RankOne μ V u.1 (T.J u.1) (T.χ u.1) ∧ V ⊓ eigL μ u.1 (T.J u.1) (T.χ u.1) ≠ ⊥) →
    ∀ (τ₀ : SmIrr (Gw n w₀.1)) (τ : ∀ v : Pl F, SmIrr (Gw n (T.mk' v).1)) (g : ∀ v : Pl F, Gw n (T.mk' v).1 →* Gw n (T.mk' v).1)
      (I : ∀ v : Pl F, (τ v).V ≃ₗ[ℂ] (τ v).V), Occurs μ V w₀.1 τ₀ → (∀ v ∈ T.S, Occurs μ V (T.mk' v).1 (τ v)) →
      (∀ v ∈ T.S, ¬ GM.Split E v → IsLocGal σ (T.mk' v) (g v) ∧ ∀ x y, I v ((τ v).ρ x y) = (τ v).ρ (g v x) (I v y)) →
      ∀ y : ℝ, 0 < y →
      ∃ c : ℂ, (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ → c ≠ 0) ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), FitsV T L ψ →
        ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 →
        ∀ (j : ℕ) (sq : ℂ) (t : Pl F → ℂ), HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • e)).indicator 1) sq →
          (∀ v ∈ T.sp, HasTrace (m (T.mk' v).1) (τ v).ρ (ψ v) (t v)) →
          (∀ v ∈ T.S, ¬ GM.Split E v → HasTwTrace (m (T.mk' v).1) (τ v) (I v) (ψ v) (t v)) →
          trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) = c * sq * ∏ v ∈ T.S, t v

end UpperTheory.ConvolutionTheory.C
