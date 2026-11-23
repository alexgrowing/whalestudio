import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant
import GroundTheory.PAdicHodge.NormalizedTrace

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL.Split

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem cuspFin_zero : CuspFin E 0 := by
  intro L hL W _ _ _ ρ hρ J hJ
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  haveI : FiniteDimensional ℂ (GA E 0 → ℂ) := inferInstance
  infer_instance

theorem invariant_of_lie_oneL_eq_zero {a : ℕ} (ψ : Sm E a) (h : lie E a (oneL E a) ψ = 0) (t : ℝ) (g : GA E a) :
    ψ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = ψ.1 g := by
  rw [CuspidalL2GL.splitCentre_comm]
  have hd : ∀ s, HasDerivAt (fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) 0 s := by
    intro s
    have := (GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre) E a ψ g s
    rwa [h] at this
  have := is_const_of_deriv_eq_zero (f := fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [CuspidalL2GL.splitCentre_zero] using this

theorem cuspFin_pos {a : ℕ} (ha : 0 < a) : CuspFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  set V := Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} with hV
  have hVC : ∀ φ ∈ V, φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := (GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms) E a L W ρ J
  set z := lie E a (oneL E a) with hz
  obtain ⟨p, hpm, hp⟩ := GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E a J hJ z (GlobalTheory.CompanionTheory.CapelliTrace.lie_oneL_mem_Zalg E a)
  obtain ⟨T, w, hTw⟩ := (GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum) p hpm
  have hstab : ∀ φ ∈ V, z φ ∈ V := by
    intro φ hφ
    obtain ⟨hg, hc⟩ := hVC φ hφ
    have key : z φ = ∑ t ∈ T, w t • rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ := by
      apply Subtype.ext
      funext g
      have h := hTw (fun k s => ((z ^ k) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
        (fun k s => by
          have h := (GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre) E a ((z ^ k) φ) g s
          rwa [← Module.End.mul_apply, ← pow_succ'] at h)
        (fun s => by
          have h0 := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (hp φ hg.2.2.2)
          simpa [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] using h0)
      simp only [pow_one, pow_zero, Module.End.one_apply, CuspidalL2GL.splitCentre_zero, mul_one] at h
      rw [h, Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [key]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
      (Submodule.subset_span ((GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem) E a L W ρ J hJ.1 φ hg hc t))
  refine (GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces) (Sm E a) z V hstab p hpm.ne_zero (fun v hv => hp v (hVC v hv).1.2.2.2) fun c => ?_
  obtain ⟨χ, L', J', hL', hJ', hχ⟩ := (GlobalTheory.CompanionTheory.CuspTwist.twist_central) E a ha L hL W ρ hρ J hJ c
  have hfin := (GlobalTheory.CompanionTheory.CuspInvariant.cuspInvFin) cuspFormsBoundedGL (GlobalTheory.CompanionTheory.UnifAlpha.unifAlpha) E a L' hL' W ρ hρ J' hJ'
  have hle : (Submodule.span ℂ {v | v ∈ V ∧ z v = c • v}).map (mulChi a χ).toLinearMap ≤
      Submodule.span ℂ {φ | φ ∈ genSpace L' ρ J' ∧ IsCuspidal φ.1 ∧
        ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} := by
    rw [Submodule.map_span_le]
    rintro v ⟨hv, hzv⟩
    obtain ⟨hg, hc⟩ := hVC v hv
    obtain ⟨h1, h2, h3⟩ := hχ v hg hc hzv
    exact Submodule.subset_span ⟨h1, h2, invariant_of_lie_oneL_eq_zero _ h3⟩
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (mulChi a χ).injective _).symm

theorem cuspFin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspFin E a := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact cuspFin_zero
  · exact cuspFin_pos ha

end GlobalTheory.CompanionTheory.CuspFinGL.Split
