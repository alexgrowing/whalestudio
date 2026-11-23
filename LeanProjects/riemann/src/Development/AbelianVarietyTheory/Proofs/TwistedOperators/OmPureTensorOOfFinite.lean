import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteFock

variable {D : D7}

theorem compAt_mt_of_finite (θ : InfFam D) (τ : D.what₂.Tau) {S : HSp D} {k : GA D S} (hk : k ∈ GfC S) :
    compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
  have h1 : (Formalism.L2.Theta.mt S k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt S k) = ((Formalism.L2.Theta.mt S k).map (infPart D)).map (θ τ) := rfl
  rw [h2, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem dRho_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [Pi.smul_apply, smul_eq_mul, ← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT) (c : ℂ)
    (f : WO S T → ℂ) (P) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, Module.End.one_apply]
  rw [dRho_smul, dRho_smul, smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem pureTensorO_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT)
    (f : WO S T → ℂ) : pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have e : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  unfold pureTensorO pureTensorL
  rw [e, Module.Basis.constr_basis]
  simp [opPow]

theorem om_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT f, (∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)) → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, ∀ c : ℂ, om (k, k') f = c • f → ∀ P, om (k, k') (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  intro D ψ θ S T χS χT om hθ hom sS sT BS BT f hf k hk k' hk' c hc P
  have hf0 : IsThetaFunO ψ S T f := by simpa only [pureTensorO_one] using hf 1
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k k'
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.one_mul]) f hf0 P).2, hc, pureTensorO_smul]

end GlobalTheory.FiniteFock
