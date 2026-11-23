import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentsOfLink
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeisOPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergComb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedThetaEqFiniteHeisenbergTranslatesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenFockGen

open GlobalTheory.SeeSaw

theorem isFockVacAt_heisO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : IsFockVacAt (heisO ψ S T) θ τ J f)
    {u : WO S T} (hu : u.map (infPart D) = 0) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T u f) := by
  have h := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf τ J hv Unit Finset.univ (fun _ => u) (fun _ => 1)
    (fun _ _ => hu)
  simpa using h

theorem heisO_pureTensorO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {u : WO S T} (hu : u.map (infPart D) = 0)
    {x : WO S T → ℂ} (hx : IsThetaFunO ψ S T x) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P) = pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u x) P := by
  classical
  have h := GlobalTheory.FiniteHeisComb.sum_heisO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (Finsupp.single u 1)
    (fun v hv => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hv
      rw [hv]; exact hu) x hx P
  simpa [Finsupp.sum_single_index] using h

theorem comb_smul' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem theta_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {c : WO S T →₀ ℂ}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u _ => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

theorem exists_defData {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D} {νS νT : ℕ}
    {PS PT : D.what₂.Tau → SPar} (hS : S.Is νS 0 PS) (hT : T.Is νT 0 PT) {a : GlobalTheory.Grid.ArrT S T}
    {χS χT : (AE D)ˣ →* Circle} (ha : a.Is ψ θ false χS χT) :
    ∃ (x : DefSp S.V) (y : DefSp T.V) (k : KerDat S.V T.V), x.Is ∧ y.Is ∧ k.Is ψ θ x y ∧ x.s = cart S.M ∧
      y.s = cart T.M ∧ x.B = onb S.M ∧ y.B = onb T.M ∧ k.om = a.ω ∧ k.vac = a.vac := by
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_vol S.V
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_vol T.V
  have pS : S.V.IsPosDef := fun τ => by rw [hS.sig τ, hS.rank, Nat.sub_zero]
  have pT : T.V.IsPosDef := fun τ => by rw [hT.sig τ, hT.rank, Nat.sub_zero]
  let x : DefSp S.V := ⟨cart S.M, onb S.M, S.Λ, vS⟩
  let y : DefSp T.V := ⟨cart T.M, onb T.M, T.Λ, vT⟩
  have hx : x.Is := GlobalTheory.SeeSawCompare.defSp_is hS.sigOK pS S.M x rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D S.V S.β S.Λ 1 hS.frame)
  have hy : y.Is := GlobalTheory.SeeSawCompare.defSp_is hT.sigOK pT T.M y rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D T.V T.β T.Λ 1 hT.frame)
  let k : KerDat S.V T.V := ⟨a.ω, a.vac, 0⟩
  have hk : k.Is ψ θ x y :=
    ⟨⟨χS, χT, (GlobalTheory.Grid.isWeil_false ψ S.V T.V χS χT a.ω).1 ha.weil⟩, ha.vac, fun u hu => (Finsupp.mem_support_iff.1 hu Finsupp.zero_apply).elim⟩
  exact ⟨x, y, k, hx, hy, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cenFock_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  intro D ψ θ hθ S T νS νT PS PT hS hT a χS χT ha χ f hf hχ
  classical
  obtain ⟨x, y, k, hx, hy, hk, hxs, hys, hxB, hyB, hkom, hkvac⟩ := exists_defData hS hT ha
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  obtain ⟨χS', χT', hW⟩ := hk.weil
  obtain ⟨Wf, -, hWf⟩ := GlobalTheory.SeeSaw.CenFockPf.cenFock D ψ θ hθ S.V T.V x y hx hy k hk χ
  obtain ⟨n, u, c, hu, hc, hlat, hsum⟩ :=
    GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua D ψ θ S.V T.V x.s y.s x.L y.L k.vac hx.sd hy.sd hk.vac f hf
  have hg : ∀ i, ∃ P, comb ψ S.V T.V (c i) f = pureTensorO ψ θ S.V T.V x.s y.s x.B y.B k.vac P := by
    intro i
    have he : ∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) →
        k.om (z, 1) (comb ψ S.V T.V (c i) f) = χ z • comb ψ S.V T.V (c i) f := by
      intro z hz hzc
      rw [GlobalTheory.SeeSaw.RealComm.om_comb D ψ S.V T.V χS' χT' k.om hW z hz (c i) (hc i) f hf, hkom, hχ z hz hzc,
        comb_smul']
    obtain ⟨P, -, hP⟩ := hWf _ (theta_comb hstd hf) (hlat i) he
    exact ⟨P, hP⟩
  choose P hP using hg
  have hvth : IsThetaFunO ψ S.V T.V a.vac := hkvac ▸ hk.vac.2.theta
  refine ⟨n, fun i => heisO ψ S.V T.V (u i) a.vac, P, fun i => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hvth (u i),
    fun τ => isFockVacAt_heisO_fin hstd hθ hvth τ _ (ha.vac.2.fock τ) (hu i)⟩, ?_⟩
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hP i, heisO_pureTensorO_fin hstd hθ _ _ _ _ (hu i) hk.vac.2.theta, hxs, hys, hxB, hyB, hkvac]
  rfl

end GlobalTheory.CenFockGen

end
