import Mathlib
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def SideCond (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal ∧ PsiUnramAt ψ v ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → w.valuation D.host.E D.host.xi0 = 1

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

def cuspidalL2Subspace : Submodule ℂ (DividedPowerChartLift V ν) :=
  (Submodule.span ℂ {x | ∃ (φ : GA D V → ℂ) (h : MemL2Quotient (GQ V) ν φ),
    IsAutFun V φ ∧ IsCuspFun V φ ∧ x = h.toL2}).topologicalClosure

def IsCuspIrr (W : Submodule ℂ (DividedPowerChartLift V ν)) : Prop := IsIrredSubrep (RG V ν) W ∧ W ≤ cuspidalL2Subspace V ν

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}

def locRep (hW : IsCuspIrr V ν W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Representation ℂ (GLoc D.sp.cm.sig V.gram v) W :=
  ((ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := W)).toMonoidHom.comp hW.1.1.rep).comp
    (emb D.sp.cm.sig V.gram v)

def SphAt (hW : IsCuspIrr V ν W) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  GlobalTheory.LGrp.IsSpherical (locRep hW v) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)

variable (W) in

def HasRealType (θ : InfFam D) (S : D.what₂.Tau → SPar) : Prop :=
  ∃ M : DSModel V S, ∀ τ, ∃ A : M.H τ →L[ℂ] DividedPowerChartLift V ν, A ≠ 0 ∧ (∀ x, A x ∈ W) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x, A (M.rep τ g x) = RG V ν (atTau θ V τ g) (A x)

def NoExcluded (hW : IsCuspIrr V ν W) (μ : (AE D)ˣ →* Circle) (t : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
    GlobalTheory.LFun.UnrAt μ w ∧ ∃ B : Multiset ℂˣ, GlobalTheory.LFun.HasParam D.sp.cm.sig V.gram (frameLat V) h (locRep hW v) B ∧
      ∀ b ∈ B, ((b * (GlobalTheory.LFun.val μ w)⁻¹ : ℂˣ) : ℂ) ∉ excluded (Formalism.UG.qV D.host.F v) t

def Conclusion (hW : IsCuspIrr V ν W) (μ : (AE D)ˣ →* Circle) (ψ : AddChar (AF D.host.F) ℂ)
    (S : Set (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  (∃ v, v ∉ S ∧ SideCond ψ v ∧ NoExcluded hW μ D.R.t v) ∧
  ∀ p : ℕ, SplitsCompletely D p → (∀ v ∈ S, (p : 𝓞 D.host.F) ∉ v.asIdeal) →
    ¬ p ∣ D.host.QS * D.host.q * D.host.d ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal →
      NoExcluded hW μ D.R.t v ∧ (p.Coprime (Ideal.absNorm D.host.ccK) → SideCond ψ v)

end Cusp

def IsAdmDatum (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (Φ : WO A B → ℂ) : Prop :=
  IsThetaFunO ψ A B Φ ∧
    IsLatVac (heisO ψ A B) (latO A B (L0c D A) (L0c D B) fun v => ¬ IsSplit (E := D.host.E) v) Φ

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

inductive IsIterLift : ∀ k, (GA D (Yc D k) → ℂ) → Prop
  | base {f : GA D (Yc D 0) → ℂ} (hf : IsAutFunSm θ (Yc D 0) f) (h : MemL2Quotient (GQ (Yc D 0)) (ν 0) f) (hσ : h.toL2 ∈ σ) :
      IsIterLift 0 f
  | step {k : ℕ} {u : GA D (Yc D k) → ℂ} (hu : IsIterLift k u) {Φ : WO (Yc D k) (Yc D (k + 1)) → ℂ}
      (hΦ : IsAdmDatum ψ (Yc D k) (Yc D (k + 1)) Φ)
      (hi : ∀ h, IntegrableOn (fun g => th k g h Φ * u g) (𝓕 k) (ν k)) :
      IsIterLift (k + 1) fun h => ∫ g in 𝓕 k, th k g h Φ * u g ∂ν k

def liftSpace (k : ℕ) : Submodule ℂ (GA D (Yc D k) → ℂ) := Submodule.span ℂ {F | IsIterLift θ ψ th ν 𝓕 σ k F}

def MeetsLift (k : ℕ) (W : Submodule ℂ (DividedPowerChartLift (Yc D k) (ν k))) : Prop :=
  ∃ F ∈ liftSpace θ ψ th ν 𝓕 σ k, ∃ h : MemL2Quotient (GQ (Yc D k)) (ν k) F, h.toL2 ∉ Wᗮ

end Chain

def typePlaces (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

def badPlaces {T : Type} (L : LevCh D T) (t : T) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  typePlaces D ∪ {v | ∃ w ∈ L.Q t, w.under (𝓞 D.host.F) = v}

def NodeChainStatement (D : D7) : Prop :=
  (∃ N : ℕ, D.R.rankY D.R.m + 1 ≤ N ∧ D.NodeGap ((D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1)) →
  ∀ (T : Type) (L : LevCh D T) (t₀ : T), L.Is t₀ → ∀ (t : T) (θ : InfFam D), IsInfFam θ →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ),
    IsChainKernel ψ (L.mu t) L.eta D.R.m (Yc D) th →
  ∀ (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
    (𝓕 : ∀ k, Set (GA D (Yc D k))), (∀ k, IsFundamentalDomain (GQ (Yc D k)) (𝓕 k) (ν k)) →
  ∀ (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0))) (hσ : IsCuspIrr (Yc D 0) (ν 0) σ),
    HasRealType σ θ (parA (tparRec D) 0) → (∀ v ∉ typePlaces D, SphAt hσ v) →
  ∀ k, k < D.R.m → ∀ (π : Submodule ℂ (DividedPowerChartLift (Yc D k) (ν k))) (hπ : IsCuspIrr (Yc D k) (ν k) π),
    MeetsLift θ ψ th ν 𝓕 σ k π →
    Conclusion hπ (chrStep (L.mu t) L.eta (k + 1)).2 ψ (badPlaces L t)

def SingleBlockCuspidal (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V : HSp D), V.rank = D.R.r →
  ∀ (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (π : Submodule ℂ (DividedPowerChartLift V ν)) (hπ : IsCuspIrr V ν π) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ S, SphAt hπ v) →
  ∀ μ : (AE D)ˣ →* Circle, IsHeckeChar D μ → GlobalTheory.LFun.UnrOff μ (S : Set _) → Conclusion hπ μ ψ (S : Set _)

def NoExcludedParameter : Prop := ∀ D : D7, NodeChainStatement D ∧ SingleBlockCuspidal D

example : (4 : ℂ) ∈ excluded 4 3 := Or.inl (by norm_num)

example {C : Type} [CommGroup C] (μ : ℕ → C) (η : C) :
    (chrStep μ η 1).2 = μ 1 ∧ (chrStep μ η 2).2 = μ 2 * η⁻¹ := by
  constructor <;> simp [chrStep, Nat.odd_iff]

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
