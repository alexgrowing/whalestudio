import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAwayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.PureTensorTrace

theorem isIntegralOp_smoothOp {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := μ) hf hc l v]
    simp only [smul_eq_mul]

theorem hasTrace_update_eq_const_mul : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ c : ℂ, ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, (∃ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b) ∧ ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V (Function.update ff u f)) (c * b) := by
  intro D V u μf hμ hK1 ν hν W _ _ σ hσ N _ _ π hπi hπa hloc ff hff
  haveI : (μf u).IsHaarMeasure := hμ u
  obtain ⟨H, K, hKo, hHc, hHf, hHop⟩ := GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace D V u μf hμ hK1 ν hν W σ hσ.1 ff hff
  have hcont : Continuous (locFin V u) := (continuous_emb _ _ u).subtype_mk _
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun x => (hσ.1 x).preimage hcont
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_localComponent_copies_fixed_away D V u W σ hσ N π hπi hπa hloc K hKo
  have hrange : ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))),
      LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
    refine ⟨s, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hs _ fun k hk hk1 => hHf x k hk hk1
  have hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id := fun φ =>
    GlobalTheory.T.schur_admissible_alt (Gv V u) (Kv V u) (isOpen_stabLoc _ _ _ u) (isCompact_stabLoc _ _ _ u) N π hπi hπa
      φ.toLinearMap fun g x => Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ := GlobalTheory.T.trace_mul_endomorphism_isotypicRep (Gv V u) N W π (σ.comp (locFin V u)) hπi hschur hloc H
    (fun g x => hHc g x) hrange
  refine ⟨c, fun f hf => ⟨?_, ?_⟩⟩
  · have hfd := hπa.finiteDimensional_range_smoothOp (μ := μf u) hf.1 hf.2 (isOpen_stabLoc _ _ _ u)
      (isCompact_stabLoc _ _ _ u) (K := Kv V u)
    exact ⟨_, _, isIntegralOp_smoothOp hπa.1 hf.1 hf.2, hfd, rfl⟩
  · rintro b ⟨A, hA, hAb⟩
    obtain rfl := hA.unique (isIntegralOp_smoothOp hπa.1 hf.1 hf.2)
    have hB := isIntegralOp_smoothOp (μ := μf u) hρ hf.1 hf.2
    refine ⟨_, hHop f hf _ hB, hc _ _ (fun φ => ?_) b hAb⟩
    ext x
    exact (hπa.1.map_smoothOp_of_intertwining hρ hf.1 hf.2 φ.toLinearMap
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ φ g v) x).symm

end GlobalTheory.PureTensorTrace
