import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Mem.Th
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

section Core

variable {X : Type} [MeasurableSpace X] {ν : Measure X}

def HasRows (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (β : X → Lp ℂ 2 ν) : Prop :=
  ∀ φ : Lp ℂ 2 ν, B φ =ᵐ[ν] fun x => ⟪β x, φ⟫_ℂ

def IsKernelOf (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  (∀ x, MemLp (K x) 2 ν) ∧ ∀ φ : Lp ℂ 2 ν, T φ =ᵐ[ν] fun x => ∫ z, K x z * φ z ∂ν

def TraceIsDiagonal (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  IsTraceClass T ∧ Integrable (fun x => K x x) ν ∧ trace T = ∫ x, K x x ∂ν

end Core

def TraceKernelCore : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    [ν.IsOpenPosMeasure] [IsSeparable ν] (n : ℕ) (B C : Fin n → (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (β γ : Fin n → X → Lp ℂ 2 ν),
    (∀ i, IsHilbertSchmidt (B i)) → (∀ i, IsHilbertSchmidt (C i)) →
    (∀ i, Continuous (β i)) → (∀ i, Continuous (γ i)) →
    (∀ i, HasRows (B i) (β i)) → (∀ i, HasRows (ContinuousLinearMap.adjoint (C i)) (γ i)) →
      (∀ i, IsKernelOf (B i ∘L C i) (fun x z => ⟪β i x, γ i z⟫_ℂ) ∧
        TraceIsDiagonal (B i ∘L C i) fun x z => ⟪β i x, γ i z⟫_ℂ) ∧
      ∀ K : X → X → ℂ, Continuous (Function.uncurry K) → IsKernelOf (∑ i, B i ∘L C i) K →
        TraceIsDiagonal (∑ i, B i ∘L C i) K

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCcInf (θ : InfF D) (V : HSp D) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧
    (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, f (g * k) = f g) ∧
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def MapsIntoCusp (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA D V → ℂ) : Prop :=
  ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ

def CuspTraceClass (θ : InfF D) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Prop :=
  ∀ f, IsCcInf θ V f → IsTraceClass (RcuspOp V μ f)

def TraceKernelAt (θ : InfF D) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Prop :=
  ∀ f, IsCcInf θ V f → MapsIntoCusp V μ f → MapsIntoCusp V μ (starFn f) →
    TraceIsDiagonal (ν := autMeasure V μ) (RopG V μ f) (kernelQ (GQ V) f)

def TraceKernel : Prop :=
  ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    CuspTraceClass θ V μ → TraceKernelAt θ V μ

def TraceKernelUncond : Prop :=
  ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    TraceKernelAt θ V μ

theorem TraceKernel.uncond (h : TraceKernel)
    (hc : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant], CuspTraceClass θ V μ) : TraceKernelUncond :=
  fun D θ hθ V μ _ _ => h D θ hθ V μ (hc D θ hθ V μ)

example (V : HSp D) (f : GA D V → ℂ) (x : GA D V) :
    kernelQ (GQ V) f (mk _ x) (mk _ x) = ∑' γ : GQ V, f (x⁻¹ * γ * x) := kernelQ_mk f x x

theorem oneP_mem_GinfC (θ : InfF D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    oneP θ V τ X t ∈ GinfC V := by
  unfold oneP atTau
  split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem isCcInf_indicator (θ : InfF D) (V : HSp D) {K : Subgroup (GA D V)} (ho : IsOpen (K : Set (GA D V)))
    (hc : IsCompact (K : Set (GA D V))) (hK : GinfC V ≤ K) :
    IsCcInf θ V ((K : Set (GA D V)).indicator fun _ => 1) := by
  have hinv : ∀ k ∈ K, ∀ g, (K : Set (GA D V)).indicator (fun _ => (1 : ℂ)) (g * k) =
      (K : Set (GA D V)).indicator (fun _ => (1 : ℂ)) g := fun k hk g => by
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem (K.mul_mem hg hk), Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_right hk).1 h)]
  have hcl : IsClopen (K : Set (GA D V)) := ⟨K.isClosed_of_isOpen ho, ho⟩
  refine ⟨hcl.continuous_indicator continuous_const, HasCompactSupport.intro' hc hcl.1 fun x hx => Set.indicator_of_notMem hx _,
    ⟨K, ho, fun k hk _ => hinv k hk⟩, fun k τs Xs _ g => ?_⟩
  have : ∀ t : Fin k → ℝ, (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ K := fun t =>
    K.list_prod_mem fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact hK (oneP_mem_GinfC θ V _ _ _)
  simp only [hinv _ (this _)]
  exact contDiff_const

theorem exists_isCcInf (θ : InfF D) (V : HSp D) (hV : V.gram = 1) : ∃ f, IsCcInf θ V f ∧ f 1 = 1 := by
  obtain ⟨K, hK, ho, -, hc⟩ := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).2.2.2.2.2.2
    (Submodule.span _ (Set.range (Pi.basisFun D.host.E (Fin V.rank)))) 1
    ⟨Submodule.fg_span (Set.finite_range _), by
      rw [Submodule.span_span_of_tower, (Pi.basisFun D.host.E (Fin V.rank)).span_eq]⟩ one_pos
  refine ⟨_, isCcInf_indicator θ V ho (hc hV) fun k hk => (hK k).2 ?_, Set.indicator_of_mem K.one_mem _⟩
  have h1 := (hK 1).1 K.one_mem
  have e : (finHom V k).1 = (finHom V 1).1 := by rw [map_one, show finHom V k = 1 from hk]
  unfold GlobalTheory.Ker.CongK at h1 ⊢
  rw [GlobalTheory.Ker.CongTop.fmt_eq] at h1 ⊢
  rwa [e]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

end
