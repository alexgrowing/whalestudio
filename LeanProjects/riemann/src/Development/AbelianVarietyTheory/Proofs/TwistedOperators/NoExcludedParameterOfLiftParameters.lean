import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSphericalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) (SelfDual.isLattice_frameLat V).span_eq_top h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

def liftParam (μ : ℕ → (AE D)ˣ →* Circle) (η : (AE D)ˣ →* Circle) (k : ℕ) (w : HeightOneSpectrum (𝓞 D.host.E))
    (B : Multiset ℂˣ) : Multiset ℂˣ :=
  (B + ∑ i ∈ Finset.range k, seg w (val (μ (i + 1)) w) D.R.t).map (· * if Odd k then (val η w)⁻¹ else 1)

def LiftParameters (D : D7) : Prop :=
  (∃ N : ℕ, D.R.rankY D.R.m + 1 ≤ N ∧ D.NodeGap ((D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1)) →
  ∀ (T : Type) (L : LevCh D T) (t₀ : T), L.Is t₀ → ∀ (t : T) (θ : InfFam D), IsInfFam θ →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ),
    IsChainKernel ψ (L.mu t) L.eta D.R.m (Yc D) th →
  ∀ (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
    (𝓕 : ∀ k, Set (GA D (Yc D k))), (∀ k, IsFundamentalDomain (GQ (Yc D k)) (𝓕 k) (ν k)) →
  ∀ (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0))) (hσ : IsCuspIrr (Yc D 0) (ν 0) σ),
    HasRealType σ θ (parA (tparRec D) 0) → (∀ v ∉ typePlaces D, SphAt hσ v) →
  ∀ k, 1 ≤ k → k < D.R.m → ∀ (π : Submodule ℂ (DividedPowerChartLift (Yc D k) (ν k))) (hπ : IsCuspIrr (Yc D k) (ν k) π),
    MeetsLift θ ψ th ν 𝓕 σ k π →
  ∀ v ∉ badPlaces L t, IsSplit (E := D.host.E) v →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (B : Multiset ℂˣ),
    HasParam D.sp.cm.sig (Yc D 0).gram (frameLat (Yc D 0)) h (locRep hσ v) B →
    HasParam D.sp.cm.sig (Yc D k).gram (frameLat (Yc D k)) h (locRep hπ v) (liftParam (L.mu t) L.eta k w B)

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

def funsOf (σ : Submodule ℂ (DividedPowerChartLift V ν)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | ∃ h : MemL2Quotient (GQ V) ν F, h.toL2 ∈ σ}
  zero_mem' := ⟨⟨fun _ _ _ => rfl, MemLp.zero⟩, by
    convert σ.zero_mem using 1
    exact MemLp.toLp_zero _⟩
  add_mem' := fun ⟨h, e⟩ ⟨h', e'⟩ => ⟨⟨fun γ hγ g => congrArg₂ (· + ·) (h.1 γ hγ g) (h'.1 γ hγ g), h.2.add h'.2⟩,
    σ.add_mem e e'⟩
  smul_mem' := fun c _ ⟨h, e⟩ => ⟨⟨fun γ hγ g => congrArg (c • ·) (h.1 γ hγ g), h.2.const_smul c⟩, σ.smul_mem c e⟩

end Zero

end GlobalTheory.NoExcl

end
