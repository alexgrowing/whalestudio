import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped ComplexConjugate Classical

namespace UpperTheory.ConvolutionTheory.L1

section One
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def eigL (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) : Submodule ℂ (LL μ) :=
  ⨅ x ∈ J, LinearMap.eqLocus (rhoL μ w x : LL μ →ₗ[ℂ] LL μ) (χ x • LinearMap.id)

def RankOne (V : Submodule ℂ (LL μ)) (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) : Prop :=
  ∀ g, ∃ c : ℂ, ∀ v ∈ V ⊓ eigL μ w J χ, prj (eigL μ w J χ) (rhoL μ w g v) = c • v

def IsChr {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) (χ : G → ℂ) : Prop :=
  IsLocallyConstant χ ∧ (∀ x ∈ J, ‖χ x‖ = 1) ∧ ∀ x ∈ J, ∀ y ∈ J, χ (x * y) = χ x * χ y

end One

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure Ty (σ : E ≃ₐ[F] E) (n : ℕ) (q : Pl F) (w₀ : PlacesOver E q) where
  S : Finset (Pl F)
  q_not : q ∉ S
  J : ∀ w : Pl E, Subgroup (Gw n w)
  χ : ∀ w : Pl E, Gw n w → ℂ
  mk' : ∀ v : Pl F, PlacesOver E v
  co : ∀ w, CO (J w)
  chr : ∀ w, IsChr (J w) (χ w)
  off : ∀ w : Pl E, w.under (𝓞 F) ∉ S → w.under (𝓞 F) ≠ q → J w = GLnLocal.integralGL (w.adicCompletion E) n ∧ χ w = 1
  at_q : ∀ w : PlacesOver E q, J w.1 = GLnLocal.iwahori (w.1.adicCompletion E) n
  triv : ∀ v : Pl F, GM.Split E v → ∀ w : PlacesOver E v, χ w.1 = 1
  stable : ∀ (v : Pl F) (x : GL (Fin n) (CompletionsOver E v)), (∀ u, GM.cmp u x ∈ J u.1) →
    (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u.1) ∧
      ∏ᶠ u : PlacesOver E v, χ u.1 (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u.1 (GM.cmp u x)

variable {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

def Ty.sp (T : Ty σ n q w₀) : Finset (Pl F) := T.S.filter fun v => GM.Split E v

def Ty.marked (T : Ty σ n q w₀) : Set (Pl E) := {w | w = w₀.1 ∨ ∃ v ∈ T.sp, w = (T.mk' v).1}

structure Ty.Fits (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) : Prop where
  S_eq : L.S = T.S
  test : ∀ v ∈ T.sp, Test (ψ v) ∧ ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g ∧ ψ v (g * u) = ψ v g
  split : ∀ v ∈ T.sp, L.φ v = GM.prodFn (Function.update
      (fun u : PlacesOver E v => ((T.J u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (T.mk' v) (ψ v)) ∧
    ∀ g, g ∈ L.UE v ↔ ∀ u, GM.cmp u g ∈ T.J u.1
  nonsplit : ∀ v ∈ T.S, ¬ GM.Split E v →
    L.φ v = GM.prodFn fun u : PlacesOver E v => (T.J u.1 : Set (Gw n u.1)).indicator fun x => conj (T.χ u.1 x)

variable (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

def OComponent (s : archGroup F n →* archGroup E n) (hs : Continuous s) (ν : Measure (archGroup F n)) [ν.IsHaarMeasure] (a : TI F n) :
    LL μ →L[ℂ] LL μ :=
  (((rightRegularRep (rationalGLOne E n) μ).compHom (archP E n) continuous_archP).compHom s hs).integrated ν
    (UnitaryRep.ccToL1 ν a)

def Ty.typed (T : Ty σ n q w₀) : Submodule ℂ (LL μ) := ⨅ w, eigL μ w (T.J w) (T.χ w)

def archEig (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) : Submodule ℂ (LL μ) := ⨅ i, eigIn ⊤ (O i) y

def Ty.Z (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) : Submodule ℂ (LL μ) :=
  V ⊓ archEig μ O y ⊓ ⨅ w ∉ T.marked, eigL μ w (T.J w) (T.χ w)

def Ty.Y (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) : Submodule ℂ (LL μ) :=
  V ⊓ archEig μ O y ⊓ T.typed μ

end Two

def SphRank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ w : Pl K, RankOne μ V w (GLnLocal.integralGL (w.adicCompletion K) n) 1

def LineRank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ (w : Pl K) (π : SmIrr (Gw n w)), Occurs μ V w π → ∀ (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ),
    CO J → IsChr J χ → (∃ e : π.V, ∀ x : π.V, (∀ g ∈ J, π.ρ g x = χ g • x) → ∃ c : ℂ, x = c • e) → RankOne μ V w J χ

def TypedEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ), (∀ w, CO (J w) ∧ IsChr (J w) (χ w)) →
    (∀ᶠ w in Filter.cofinite, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) →
    (∀ w, V ⊓ eigL μ w (J w) (χ w) ≠ ⊥) → V ⊓ ⨅ w, eigL μ w (J w) (χ w) ≠ ⊥

def EigBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w))
    (χ : Gw n w → ℂ), CO J → IsChr J χ → IsClosed (eigL μ w J χ : Set (LL μ)) ∧ eigL μ w J 1 = fixL μ w J ∧
    (∀ [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure], m J = 1 →
      IsOloc μ w m ((J : Set (Gw n w)).indicator fun x => conj (χ x)) (prj (eigL μ w J χ))) ∧
    ∀ B : LL μ →L[ℂ] LL μ, (∀ x ∈ J, Commute B (rhoL μ w x)) → Commute B (prj (eigL μ w J χ))

def RestScalar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ), (∀ w, CO (J w) ∧ IsChr (J w) (χ w)) →
    (∀ᶠ w in Filter.cofinite, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) → ∀ P : Set (Pl K),
    (∀ w ∉ P, RankOne μ V w (J w) (χ w)) → ∀ h : AdelicGLn.FiniteAdelicGL K n, (∀ w ∈ P, finAt w (finEmb K n h) = 1) →
    ∃ c : ℂ, ∀ v ∈ V ⊓ ⨅ w ∉ P, eigL μ w (J w) (χ w), prj (⨅ w ∉ P, eigL μ w (J w) (χ w)) (rhoF μ h v) = c • v

def TensFactor : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ),
    (∀ w, CO (J w) ∧ IsChr (J w) (χ w)) →
    (∀ᶠ w in Filter.cofinite, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) → ∃ κ : ℝ, 0 < κ ∧
    ∀ (β : TI K n) (r : ℕ) (w : Fin r → Pl K), Function.Injective w →
    ∀ [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))] (m : ∀ i, Measure (Gw n (w i))),
      (∀ i, (m i).IsHaarMeasure ∧ m i (J (w i)) = 1) → ∀ (ψ : ∀ i, Gw n (w i) → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ),
      (∀ i, Test (ψ i) ∧ (∀ u ∈ J (w i), ∀ g, ψ i (g * u) = conj (χ (w i) u) * ψ i g) ∧ IsOloc μ (w i) (m i) (ψ i) (T i)) →
      ∀ e : TF K n, (∀ x, e x = (∏ i, ψ i (finAt (w i) (finEmb K n x))) *
        ∏ᶠ u ∉ Set.range w, (J u : Set (Gw n u)).indicator (fun g => conj (χ u g)) (finAt u (finEmb K n x))) →
      RR μ (tens β e) = (κ : ℂ) • (Oinf μ ν β ∘L (List.ofFn T).prod ∘L prj (⨅ u, eigL μ u (J u) (χ u)))

def TwistPerm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ (m n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    (∀ (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n), IsBlockElement D n s → ∀ i g v,
      θ.U (rightRegularRep (rationalGLOne E n) μ (archP E n (s (i + 1) g)) v) =
        rightRegularRep (rationalGLOne E n) μ (archP E n (s i g)) (θ.U v)) ∧
    (∀ (p : Pl F) (D : Split (incFin E p) (galFin σ p) m) (w : Fin (m + 1) ≃ PlacesOver E p),
      (∀ (b : CompletionsOver E p) i, completionMap p (w i).1 (D.e b i) = b (w i)) → ∀ i g v,
      θ.U (rhoL μ (w (i + 1)).1 (mapGL n (completionMap p (w (i + 1)).1) g) v) =
        rhoL μ (w i).1 (mapGL n (completionMap p (w i).1) g) (θ.U v)) ∧
    ∀ (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀) (P : Set (Pl F)),
      Commute θ.U (prj (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)))

def ZBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n)
      (hs : ∀ i, Continuous (s i)), IsBlockElement D n s → ∀ (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (a : TI F n)
      (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
    ∀ y : ℝ, 0 < y →
      IsClosed (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y : Set (LL μ)) ∧
      (∀ w ∈ T.marked, ∀ g, ∀ v ∈ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y,
        rhoL μ w g v ∈ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y) ∧
      (∀ U : ∀ w : Pl E, Subgroup (Gw n w), (∀ w ∈ T.marked, CO (U w)) →
        FiniteDimensional ℂ ↥(T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ⊓ ⨅ w ∈ T.marked, fixL μ w (U w))) ∧
      T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y =
        T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ⊓ ⨅ w ∈ T.marked, fixL μ w (T.J w)

def TwistY : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ m n : ℕ, Module.finrank F E = m + 1 → 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v, RankOne μ V u.1 (T.J u.1) (T.χ u.1)) →
      ((∃ v ∈ V ⊓ T.typed μ, OComponent μ (s 0) (hs 0) νF a v ≠ 0) →
        ∃ y : ℝ, 0 < y ∧ T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥) ∧
      ∀ y : ℝ, 0 < y → ∃ c : ℂ, c ≠ 0 ∧ ∀ B : LL μ →L[ℂ] LL μ,
        (∀ g, Commute B (rightRegularRep (rationalGLOne E n) μ (archP E n g))) →
        (∀ w ∉ T.marked, ∀ g, Commute B (rhoL μ w g)) →
        trOn (eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) (y ^ (m + 1))) (B ∘L θ.U) =
          c * trOn (T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y) B

def SideTrace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ m n : ℕ, Module.finrank F E = m + 1 → 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v, RankOne μ V u.1 (T.J u.1) (T.χ u.1)) →
      ∀ y : ℝ, 0 < y → ∃ c : ℂ, c ≠ 0 ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
        ∀ (ν : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), GM.IsSideE L νE aE ν 𝔢 →
        ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ T.sp ↔ v ∈ Set.range p) →
        ∀ [∀ i, MeasurableSpace (Gw n (T.mk' (p i)).1)] [∀ i, BorelSpace (Gw n (T.mk' (p i)).1)]
          (mm : ∀ i, Measure (Gw n (T.mk' (p i)).1)), (∀ i, (mm i).IsHaarMeasure ∧ mm i (T.J (T.mk' (p i)).1) = 1) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm i) (ψ (p i)) (B i)) → ∀ j : ℕ,
          trOn (eigIn V 𝔢.toAmp.A (y ^ (m + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) =
            c * trOn (T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y) ((Uiw μ w₀.1 ν ^ j) ∘L (List.ofFn B).prod)

end UpperTheory.ConvolutionTheory.L1
