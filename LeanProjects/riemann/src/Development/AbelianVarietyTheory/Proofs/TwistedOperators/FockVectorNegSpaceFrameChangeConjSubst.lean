import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockNegSubst

open MvPolynomial

theorem map_conj_substF {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.CompactHowe.substF h g P) =
      GlobalTheory.CompactHowe.substF (fun τ => (h τ).map (starRingEnd ℂ)) (fun τ => (g τ).map (starRingEnd ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [GlobalTheory.CompactHowe.substF, MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, RingHom.id_apply]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul (GlobalTheory.CompactHowe.substF h g), map_mul (MvPolynomial.map (starRingEnd ℂ)), hp,
      map_mul (MvPolynomial.map (starRingEnd ℂ)), map_mul, MvPolynomial.map_X, GlobalTheory.CompactHowe.substF_X,
      GlobalTheory.CompactHowe.substF_X]
    congr 1
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

theorem map_conj_conj {σ : Type} (P : MvPolynomial σ ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => Complex.conj_conj z
  rw [e, MvPolynomial.map_id]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_map_conj {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (MvPolynomial.map (starRingEnd ℂ) Q) =
      fun x => starRingEnd ℂ (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT
        (fun w => starRingEnd ℂ (f w)) Q x) := by
  funext x
  induction Q using MvPolynomial.induction_on' with
  | monomial k a =>
    have hm := GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f hψ hθ k x
    have e1 : (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) =
        (starRingEnd ℂ a) • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, e1, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ← hm]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hp, hq, map_add]

end GlobalTheory.FockNegSubst

namespace GlobalTheory.FockNegSubst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT v : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ), IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f P = pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (v τ).map (starRingEnd ℂ)) (fun τ => (((u τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T hψ hθ BS u BT v f hf P
  have hf' : IsThetaFunO ψ S T (fun w => starRingEnd ℂ (f w)) := GlobalTheory.CjNeg.theta_negS' hψ hf
  rw [← map_conj_conj P,
    pureTensorO_negSp_map_conj ψ θ S T hψ hθ (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f
      (MvPolynomial.map (starRingEnd ℂ) P),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS u BT v _ hf' (MvPolynomial.map (starRingEnd ℂ) P),
    ← map_conj_substF, pureTensorO_negSp_map_conj ψ θ S T hψ hθ BS BT f]

end GlobalTheory.FockNegSubst
