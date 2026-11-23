import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult
open GlobalTheory.Orb (TypeDataG CcGA ResF)
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev radicalTwo (k : Type) [CommRing k] {a b r : ℕ} (h : a + b = r) : Subgroup (GL (Fin r) k) :=
  GlobalTheory.SmGL.unipRad k (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def NoRadicalFixed {V : HSp D} (T : TypeDataG V) : Prop :=
  ∀ (a b : ℕ) (h : a + b = V.rank), 0 < a → 0 < b → ∃ v : T.S, fixed (T.τ v) (radicalTwo (ResF v.1) h) = ⊥

def RadicalIntegralsVanish (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ 𝔉 : IsoFlag V, 𝔉.Proper → ∀ ν : Measure (NA 𝔉), ν.IsHaarMeasure →
    ∀ x y : GA D V, ∫ n : NA 𝔉, f (x * (n : GA D V) * y) ∂ν = 0

variable (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

structure IsCuspidalOp (f : GA D V → ℂ) : Prop where

  map_mem : ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ

  map_orthogonal : ∀ F ∈ (L2cusp V μ)ᗮ, RopG V μ f F = 0

  traceClass : IsTraceClass (RopG V μ f)

  integrable_kernel : ∀ (F : DividedPowerChartLift V μ) (p : Quot (GQ V)),
    Integrable (fun q => kernelQ (GQ V) f p q * F q) (autMeasure V μ)

  apply_eq_kernel : ∀ F : DividedPowerChartLift V μ,
    RopG V μ f F =ᵐ[autMeasure V μ] fun p => ∫ q, kernelQ (GQ V) f p q * F q ∂autMeasure V μ

  integrable_diag : Integrable (fun p => kernelQ (GQ V) f p p) (autMeasure V μ)

  trace_eq_integral : trace (RopG V μ f) = ∫ p, kernelQ (GQ V) f p p ∂autMeasure V μ

  mult_finite : ∀ c : UDual (GA D V), mCusp V μ c.rep.π < Cardinal.aleph0

  traceClass_rep : ∀ c : UDual (GA D V), mCusp V μ c.rep.π ≠ 0 → IsTraceClass (repOp c.rep.π μ f)

  summable_norm : Summable fun c : UDual (GA D V) => ‖((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f‖

  hasSum_trace : HasSum (fun c : UDual (GA D V) => ((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f)
    (trace (RopG V μ f))

def CuspidalOperators : Prop :=
  ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → RadicalIntegralsVanish V (starFn f) → IsCuspidalOp V μ f

def CopiesCuspidal (T : TypeDataG V) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)),
    IsIrrUnitary π → ContainsTypes T (finRes π) →
      (∀ U ≤ L2discG V μ, IsCopy π (RG V μ) U → U ≤ L2cusp V μ) ∧ mDisc V μ π = mCusp V μ π

def TensorCopiesCuspidal (T : TypeDataG V) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    σ.IsIrreducible → IsAdmissible σ → ContainsTypes T σ →
      ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (δ : GinfC V →* (X →L[ℂ] X)), IsIrrUnitary δ →
        (∀ U ≤ L2discG V μ, IsCopyFinInf V σ δ (RG V μ) U → U ≤ L2cusp V μ) ∧ mDiscT V μ σ δ = mCuspT V μ σ δ

def DiscreteSeriesCopiesCuspidal (T : TypeDataG V) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    σ.IsIrreducible → IsAdmissible σ → ContainsTypes T σ →
      ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S),
        (∀ U ≤ L2discG V μ, IsCopyFinDS σ M (RG V μ) U → U ≤ L2cusp V μ) ∧ mDiscDS μ σ M = mCuspDS μ σ M

def TypesForceCuspidal : Prop :=
  ∀ T : TypeDataG V, T.S.Nonempty → NoRadicalFixed T →
    CopiesCuspidal V μ T ∧ TensorCopiesCuspidal V μ T ∧ DiscreteSeriesCopiesCuspidal V μ T

def Statement : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    CuspidalOperators V μ ∧ TypesForceCuspidal V μ

example {f : GA D V → ℂ} (hf : f ∈ CcGA V) (x y : GA D V) : Summable fun γ : GQ V => f (x⁻¹ * γ * y) :=
  (hasSum_kernel (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2 x y).summable

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem containsTypes_finRes {H X W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}
    {δ : GinfC V →* (X →L[ℂ] X)} {π : GA D V →* (H →L[ℂ] H)} {U : Submodule ℂ H} (h : IsCopyFinInf V σ δ π U)
    {T : TypeDataG V} (hT : ContainsTypes T σ) : ContainsTypes T (finRes π) := fun v => by
  obtain ⟨Φ, hΦ, hi, -⟩ := h
  obtain ⟨f, h0, e⟩ := contains_iff.1 (hT v)
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.1 h0
  have h1 : Φ (f z) ≠ 0 := fun h => hz (hi (h.trans (map_zero Φ).symm))
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 h1
  refine contains_iff.2 ⟨(ContinuousLinearMap.apply ℂ H y).toLinearMap ∘ₗ Φ ∘ₗ f, DFunLike.ne_iff.2 ⟨z, hy⟩,
    fun g x => ?_⟩
  exact (congrArg (fun w => Φ w y) (e g x)).trans ((mem_homTensor.1 hΦ).2.1 _ _ y)

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

example (h : V.rank = 1) (T : TypeDataG V) : NoRadicalFixed T := fun a b e ha hb => by omega

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

end
