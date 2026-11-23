import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.FiniteHeis

variable {D : D7}

noncomputable def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lineAt_fin {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    (show WO S T from lineAt θ τ z t).map (finPart D) = 0 :=
  (Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ T.rank S.rank τ z)).2.1 t

theorem heisO_comm_real (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {u x : WO S T} (hu : u.map (infPart D) = 0)
    (hx : x.map (finPart D) = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).1,
    (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).2, add_comm]

theorem heisO_dRho (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (dRho (heisO ψ S T) θ τ z g) = dRho (heisO ψ S T) θ τ z (heisO ψ S T u g) := by
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) =
      fun t : ℝ => ψ (symplOH S T x u) * heisO ψ S T (lineAt θ τ z t) g (x + u) := by
    funext t
    rw [← heisO_comm_real ψ hu (lineAt_fin hθ τ z t) g]
    rfl
  show ψ (symplOH S T x u) * deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) g (x + u)) 0 =
    deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) 0
  rw [e, deriv_const_mul_field]

theorem heisO_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsInfFam θ → ∀ sS sT BS BT f, (∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) → ∀ u : WO S T, u.map (infPart D) = 0 → heisO ψ S T u f = f → ∀ φ, heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := by
  intro D ψ θ S T hθ sS sT BS BT f _ u hu hf φ
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (heisLin ψ S T u)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial φ).2
  · have hf' : heisLin ψ S T u f = f := hf
    rw [hf'] at h
    exact h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T u (Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Datum.dRho _ _ _ _ _)) = _
    rw [heisO_dRho ψ hθ hu, heisO_dRho ψ hθ hu]
    rfl

end GlobalTheory.Hk3.FiniteHeis
