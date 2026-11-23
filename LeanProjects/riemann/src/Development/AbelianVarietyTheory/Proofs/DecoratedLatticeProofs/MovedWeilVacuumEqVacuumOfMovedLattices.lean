import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedVac

theorem halfBack : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (u : WO S T),
    IsHalf e (actO S T g h u) → IsHalf e u := by
  intro D S T g h e u hu
  have hA : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom T h))
  have hB : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom S g))
  have cancel : ∀ X : Matrix (Fin T.rank) (Fin S.rank) (AE D),
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) X)
        (Formalism.L2.Theta.mt S g⁻¹))) (Formalism.L2.Theta.mt S g) = X := by
    intro X
    simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have key : e • actO S T g h u = actO S T g h u := by
    ext i j; exact hu i j
  have key2 : e • u = u := by
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) M) (Formalism.L2.Theta.mt S g)) key
    simp only [actO] at h1
    rw [cancel u] at h1
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h1
    rw [cancel u] at h1
    exact h1
  intro i j
  have := congrFun (congrFun key2 i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem norm_weilRepresentation_thetaFunction_preserved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T μ μ om → ∀ f, IsThetaFunO ψ S T f → ∀ p (m : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) m 𝓕 → nrm2 m 𝓕 (om p f) = nrm2 m 𝓕 f := by
  intro D ψ S T μ om hW f hf p m 𝓕 hm
  have hU := hW.om_unit m 𝓕 hm.1 hm.2.1 p f hf
  have hf' := hW.om_pres p f hf
  haveI : OpensMeasurableSpace (WO S T) := ⟨le_rfl⟩
  have key : ∀ F : WO S T → ℂ, Continuous F → nrm2 m 𝓕 F = (∫⁻ w in 𝓕, ‖F w‖ₑ ^ 2 ∂m).toReal := by
    intro F hF
    unfold nrm2
    have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
      (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [key _ hf'.cont, key _ hf.cont, hU]

theorem latMove : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' →
    ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True),
      ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate

theorem latSign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v →
    ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := GlobalTheory.T.heisenberg_fixes_latticeVacuum_periodLattice

theorem lamPre : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N',
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧
      embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice

theorem fixedLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc)
      (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl x hx z
  obtain ⟨γ, hγ, rfl, v, hv⟩ := lamPre D S T a b hS hT δ N N' x hx
  have hs := latSign D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl γ hγ v hv
  have hu := GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  rw [← hu]
  simp only [xiN]
  rw [← hs]
  ring

theorem vac_moved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) ∧ xiN θ S T hS hT δ sc (om (g, h) f) ∈ Formalism.L2.Th1.H.Th (HV sc) (alV D.host.d sc) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ∧ xiN θ S T hS hT δ sc (om (g, h) f) ≠ 0 := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW f hf g hg h hh N N' hN hN'
  obtain ⟨hstd, hv⟩ := hf
  have hhol : IsHol θ S T ψ f := ⟨hv.theta, hv.fock⟩
  have hI := GlobalTheory.T.om_pureTensorO_comm D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh f hhol
  have hth' : IsThetaFunO ψ S T (om (g, h) f) := hW.om_pres _ f hv.theta
  have hvac : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) := by
    refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ?_, fock := hI.1.2, norm := ?_ }⟩
    · refine ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        have h2 : actO S T g h u + actO S T g h u = actO S T g h (u + u) := by
          simp only [actO, Matrix.mul_add, Matrix.add_mul]
        have h3 := hv.lat.1 u hu
        rw [two_nsmul] at h3 ⊢
        rw [h2, ← hW.om_heis g h _ f hv.theta, h3]
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        rw [← hW.om_heis g h u f hv.theta, hv.lat.2 e he u hu (halfBack D S T g h e u hhalf)]
    · refine ⟨hv.norm.1, fun p hp => ?_⟩
      show nrm2 p.1 p.2 (om (g, h) f) = 1
      rw [norm_weilRepresentation_thetaFunction_preserved D ψ S T μ om hW f hv.theta (g, h) p.1 p.2 hp]
      exact hv.norm.2 p hp
  have hne : om (g, h) f ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := hvac.2.norm.1
    have h1 := hvac.2.norm.2 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hII := GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective D ψ θ S T a b hS hT δ sc hP
  refine ⟨hvac, ⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable (hII.1 _ hI.1) _,
    fixedLine D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' _ hth' hvac.2.lat⟩, fun h0 => hne (hII.2 _ hth' h0)⟩

end GlobalTheory.MovedVac
