import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.DiagDeriv

variable {D : D7}

theorem compAt_mul_rat (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n k : ℕ} (w : Mx D m n)
    (Q : Matrix (Fin n) (Fin k) D.host.E) : compAt θ τ (w * rat Q) = compAt θ τ w * Q.map (tauE D τ) := by
  have h : compAt θ τ (w * rat Q) = (w * rat Q).map ((θ τ).comp (infPart D)) := rfl
  rw [h, Matrix.map_mul]
  congr 1
  ext i j
  exact (hθ τ).1 (Q i j)

theorem isLineAt_extX (θ : InfFam D) (hθ : IsInfFam θ) (A B : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) (L : ℝ →+ Mx D B.rank A.rank) (hL : IsLineAt θ τ X L) :
    IsLineAt θ τ (X * (dblDec A).qX.map (tauE D τ)) (((dblDec A).extX B).comp L) := by
  refine ⟨(continuous_id.matrix_mul continuous_const).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
  · show ((L t) * (dblDec A).pX).map (finPart D) = 0
    rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
  · show compAt θ τ' (L t * rat (dblDec A).qX) = _
    rw [compAt_mul_rat θ hθ, hL.2.2 t τ']
    split_ifs with h
    · subst h; rw [Matrix.smul_mul]
    · rw [Matrix.zero_mul]

theorem lineAt_isLineAt (θ : InfFam D) (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) : IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem lineAt_extX (θ : InfFam D) (hθ : IsInfFam θ) (A B : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) :
    (lineAt θ τ (X * (dblDec A).qX.map (tauE D τ)) : ℝ →+ WO (dblSp A) B) =
      ((dblDec A).extX B).comp (lineAt θ τ X) :=
  GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (lineAt_isLineAt θ hθ τ _)
    (isLineAt_extX θ hθ A B τ X _ (lineAt_isLineAt θ hθ τ X))

theorem hasDerivAt_mixS_extX {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (M : ℝ →+ WO S T) (hM : IsRealDir T S M) (x : Mx D T.rank ρ) (w : WO S₀ T) :
    HasDerivAt (fun t : ℝ => d.mixS T ψ μ 𝓕 (heisO ψ S T (M t) f) x w)
      (d.mixS T ψ μ 𝓕 (GlobalTheory.OrientedHeis.dLine ψ S T M f) x w) 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hM hf)
  have e2 : GlobalTheory.OrientedHeis.dLine ψ S T M f = heisO ψ S T (M 0) (GlobalTheory.OrientedHeis.dLine ψ S T M f) := by
    rw [M.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
  rw [e2]
  have hI : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IntegrableOn (fun a => ψ (symplOH S T (d.extY T a) (d.extX T x)) *
      g (d.extY T a + d.extX T x + d.ext0 T w)) 𝓕 μ := fun g hg => by
    simpa only [HypDec.integrandS_eq] using HypDec.integrableOn_mixS d hψ.1.1 hμ hg x w
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
    (F' := fun t a => ψ (symplOH S T (d.extY T a) (d.extX T x)) *
      heisO ψ S T (M t) (GlobalTheory.OrientedHeis.dLine ψ S T M f) (d.extY T a + d.extX T x + d.ext0 T w))
    (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
  · exact Filter.Eventually.of_forall fun t =>
      (hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 t) hf)).aestronglyMeasurable
  · exact hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 0) hf)
  · exact (hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 0)
      (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hM hf))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a t _ => ?_
    rw [norm_mul, hψ.1.2.1, one_mul]
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hK _
  · exact Filter.Eventually.of_forall fun a t _ =>
      (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hM hf _ t).const_mul _

theorem sch_dRho_diag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ
      (X * (dblDec A).qX.map (tauE D τ)) f) x = deriv (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) 0 := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν f hf τ X x
  let v : GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  let M : ℝ →+ WO (dblSp A) B := ((dblDec A).extX B).comp (lineAt θ τ X)
  have hL := lineAt_isLineAt θ hθ τ X
  have hM : IsRealDir B (dblSp A) M := by
    refine ⟨(continuous_id.matrix_mul continuous_const).comp hL.1, fun t => ?_⟩
    show ((lineAt θ τ X t) * (dblDec A).pX).map (finPart D) = 0
    rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
  have e1 : (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) =
      fun t => (dblDec A).mixS B ψ ν 𝓨 (heisO ψ (dblSp A) B (M t) f) x 0 := by
    funext t
    have h := congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) v f hf).1 x
      (lineAt θ τ X t)) 0
    exact h.symm
  rw [e1, (hasDerivAt_mixS_extX hψ hθ (dblDec A) (μ := ν) (𝓕 := 𝓨) hν hf M hM x 0).deriv]
  show (dblDec A).mixS B ψ ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ
      (X * (dblDec A).qX.map (tauE D τ)) f) x 0 = _
  rw [GlobalTheory.OrientedHeis.dRho_eq_dLine, lineAt_extX θ hθ A B τ X]

end GlobalTheory.StdUnn.DiagDeriv
