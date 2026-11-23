import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsL2AdelicQuotientModelEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOfContinuousRepresentativeStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open GlobalTheory.HolDict GlobalTheory.BackForm
open scoped Classical

namespace GlobalTheory.CuspRepr

set_option maxHeartbeats 4000000 in

theorem exists_allMaps : ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ), ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → (∀ k ∈ K, ∀ y, RG V μ (k : GA D V) (Φ y) = Φ y) → ∃ T ∈ GlobalTheory.CuspMult.allMaps θ M, ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v := by
  intro D θ hθ V S M μ _ _ Φ hΦ K hK hKfix
  obtain ⟨𝓕, ρ, e, hp, hρ, he, hrep⟩ := GlobalTheory.T.exists_L2AdelicQuotient_model_equivalence D V μ
  obtain ⟨hcusp, hequiv⟩ := (GlobalTheory.AutMult.mem_homDS hθ).1 hΦ
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), ∀ y, Φ' y = e (Φ y) :=
    ⟨(e.toContinuousLinearEquiv : DividedPowerChartLift V μ →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕)).compContinuousMultilinearMap Φ, fun _ => rfl⟩
  have e2 : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ' (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ' y) := by
    intro τ g hg y
    rw [hΦ', hΦ', hequiv τ g hg y, he]
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  let U : Subgroup (GA D V) := K.comap (GlobalTheory.AutMult.toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hK.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ' y) = Φ' y := by
    intro y k hk hk'
    have h1 : (⟨k, hk'⟩ : GfC V) ∈ K := by
      have h2 : GlobalTheory.AutMult.toFin V k ∈ K := hk
      rwa [show GlobalTheory.AutMult.toFin V k = ⟨k, hk'⟩ from GlobalTheory.AutMult.toFin_coe (⟨k, hk'⟩ : GfC V)] at h2
    rw [hΦ', ← he]
    exact congrArg e (hKfix _ h1 y)
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ' e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ' fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  have p1' : ∀ y : M.Vec, Repr V μ 𝓕 (e (Φ fun τ => (y τ : M.H τ))) (ψ y) := fun y => hΦ' _ ▸ p1 y
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ' fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ'.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ'.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  have hEq : GlobalTheory.RepSmooth.IsEquiv θ T := by
    intro τ g hg y z hz
    refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  have hSob : GlobalTheory.RepSmooth.IsSob T := by
    intro τ y x
    obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ' T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this
  have hmult : IsMultMap θ M ∅ (fun _ => 1) T := by
    refine ⟨fun y => ⟨p2 y, p3 y, GlobalTheory.RepSmooth.zfin hEq hSob y, N, fun l hl x => ?_⟩, fun y => ?_,
      fun y k hk => hk.elim, hEq, hSob⟩
    · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
      obtain ⟨C, hC⟩ := hgr x
      refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ' fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
      rw [hy', mul_right_comm]
      exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
    · exact GlobalTheory.T.cuspidal_of_continuous_representative D V μ _ (hcusp _) (ψ y) (p2 y).cont (p2 y).left ((hrep _ _).1 (p1' y))
  exact ⟨T, Submodule.subset_span hmult, fun v => (hrep _ _).1 (p1' v)⟩

end GlobalTheory.CuspRepr
