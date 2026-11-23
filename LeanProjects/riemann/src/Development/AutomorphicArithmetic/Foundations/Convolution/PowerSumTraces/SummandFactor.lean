import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open scoped InnerProductSpace Classical

namespace UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev Gw (n : ℕ) (w : Pl K) : Type := GL (Fin n) (w.adicCompletion K)

def IsOloc (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) [MeasurableSpace (Gw n w)] (m : Measure (Gw n w))
    (φ : Gw n w → ℂ) (T : LL μ →L[ℂ] LL μ) : Prop :=
  ∀ u v : LL μ, ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, rhoL μ w g v⟫_ℂ ∂m

def Occurs (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) (w : Pl K) (σ : SmIrr (Gw n w)) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] LL μ, f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (σ.ρ g x) = rhoL μ w g (f x)

def CO {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) : Prop := IsCompact (U : Set G) ∧ IsOpen (U : Set G)

def Test {G : Type} [TopologicalSpace G] (φ : G → ℂ) : Prop := IsLocallyConstant φ ∧ HasCompactSupport φ

def OlocEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
    [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (φ : Gw n w → ℂ), Test φ →
    ∃! T, IsOloc μ w m φ T

def HopOloc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
    [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (J : Subgroup (Gw n w))
    (x : Gw n w), CO J → m J = 1 →
    IsOloc μ w m (Set.indicator {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} 1) (Hop μ w J x)

def OccursIff : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (w : Pl K) (σ : SmIrr (Gw n w)),
    Occurs μ V w σ ↔ ∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = Dp.locOn hV w g (f x)

def SummandFactor : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V Z : Submodule ℂ (LL μ))
    (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
    (σ : ∀ i, SmIrr (Gw n (w i))), IsSummand μ V → Function.Injective w → (∀ i, Occurs μ V (w i) (σ i)) →
    Z ≤ V → Z ≠ ⊥ → IsClosed (Z : Set (LL μ)) → (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) →
    (∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (U i))) →
    ∃ N : ℕ, 0 < N ∧ ∀ (U : ∀ i, Subgroup (Gw n (w i))) (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ)
      (T : Fin r → LL μ →L[ℂ] LL μ) (s : Fin r → ℂ), (∀ i, CO (U i)) → (∀ i, (m i).IsHaarMeasure) → (∀ i, Test (φ i)) →
      (∀ i, ∀ u ∈ U i, ∀ g, φ i (u * g) = φ i g) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ i, HasTrace (m i) (σ i).ρ (φ i) (s i)) →
      trOn (Z ⊓ ⨅ i, fixL μ (w i) (U i)) (List.ofFn T).prod = N * ∏ i, s i

def OccursBasics : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ))
    (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure], IsSummand μ V →
    (∃ σ, Occurs μ V w σ) ∧ (∀ σ σ', Occurs μ V w σ → Occurs μ V w σ' → Nonempty (σ.ρ.Equiv σ'.ρ)) ∧
      ∀ σ, Occurs μ V w σ → ∀ φ, Test φ → ∃ s, HasTrace m σ.ρ φ s

def CharIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (U : Subgroup G), CO U → ∀ (ι : Type) [Fintype ι] (σ : ι → SmIrr G) (c : ι → ℂ),
    (∀ i, FiniteDimensional ℂ (fixedVectors (σ i).ρ U)) →
    (∀ (φ : G → ℂ) (s : ι → ℂ), Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
      (∀ i, HasTrace m (σ i).ρ φ (s i)) → ∑ i, c i * s i = 0) →
    ∀ i₀, fixedVectors (σ i₀).ρ U ≠ ⊥ → ∑ᶠ i ∈ {i | Nonempty ((σ i).ρ.Equiv (σ i₀).ρ)}, c i = 0

def IwPow : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)]
    (m : Measure (Gw n w)) [m.IsHaarMeasure], m (GLnLocal.iwahori (w.adicCompletion K) n) = 1 →
    ∀ (σ : SmIrr (Gw n w)) (ν : Fin n → ℤ), Antitone ν →
    FiniteDimensional ℂ (fixedVectors σ.ρ (GLnLocal.iwahori (w.adicCompletion K) n)) →
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ (fixedVectors σ.ρ (GLnLocal.iwahori (w.adicCompletion K) n)) ∧
      ∀ j : ℕ, HasTrace m σ.ρ (Set.indicator {g | ∃ a ∈ GLnLocal.iwahori (w.adicCompletion K) n,
        ∃ b ∈ GLnLocal.iwahori (w.adicCompletion K) n, g = a * Cartan.diagPow (w.adicCompletion K) n (j • ν) * b} 1)
        (Z.map (· ^ j)).sum

def UiwPow : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (ν : Fin n → ℤ),
    Antitone ν → ∀ j : ℕ, (Uiw μ w ν ^ j) ∘L prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion K) n)) = Uiw μ w (j • ν)

def PowIndep : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (Z : ι → Multiset ℂ), (∀ i, 0 ∉ Z i) →
    (∀ᶠ j : ℕ in atTop, ∑ i, c i * ((Z i).map (· ^ j)).sum = 0) →
    ∀ ζ : ℂ, ∑ i, c i * (Multiset.filter (· = ζ) (Z i)).card = 0

end UpperTheory.ConvolutionTheory.C
