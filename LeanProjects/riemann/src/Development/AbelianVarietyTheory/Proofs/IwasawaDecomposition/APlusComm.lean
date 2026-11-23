import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex
open scoped Real Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

noncomputable def dirPt (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) : RW T S :=
  (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)

theorem dRho_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (∀ f', IsThetaFunO ψ S T f' → Datum.dRho (heisO ψ S T) θ τ z (f + f') =
      Datum.dRho (heisO ψ S T) θ τ z f + Datum.dRho (heisO ψ S T) θ τ z f') ∧
    (∀ a : ℂ, Datum.dRho (heisO ψ S T) θ τ z (a • f) = a • Datum.dRho (heisO ψ S T) θ τ z f) ∧
    (∀ z', Datum.dRho (heisO ψ S T) θ τ (z + z') f =
      Datum.dRho (heisO ψ S T) θ τ z f + Datum.dRho (heisO ψ S T) θ τ z' f) ∧
    (∀ t : ℝ, Datum.dRho (heisO ψ S T) θ τ ((t : ℂ) • z) f = (t : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f) ∧
    ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) -
        Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) =
      (-(2 * π * I) * (omO S T (dirPt τ z) (dirPt τ' z') : ℝ)) • f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ τ z g, Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (dirPt τ z) g := fun τ z g => by
    have := dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ] at this
    exact this
  have hs := theta_sm h hf
  have hd : ∀ {g}, IsThetaFunO ψ S T g → ∀ w, DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun hg w => ((theta_sm h hg w).differentiable (by simp)).differentiableAt
  refine ⟨fun f' hf' => ?_, fun a => ?_, fun z' => ?_, fun t => ?_, fun τ' z' => ?_⟩
  · funext w
    rw [Pi.add_apply, hE, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_add hf hf')), hD_eq_fderiv _ _ _ _ hs,
      hD_eq_fderiv _ _ _ _ (theta_sm h hf')]
    have e : (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        fun x : RW T S => f (w + iotaW σ T S x) + f' (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_add (hd hf w) (hd hf' w), ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  · funext w
    rw [Pi.smul_apply, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_smul a hf)), hD_eq_fderiv _ _ _ _ hs]
    have e : (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        fun x : RW T S => a • f (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_const_smul (hd hf w), ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  · have e : dirPt τ (z + z') = dirPt τ z + dirPt τ z' := by
      unfold dirPt
      rw [Pi.single_add]
      rfl
    funext w
    rw [Pi.add_apply, hE, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
      LinearMap.map_add, ContinuousLinearMap.map_add]
    push_cast
    ring
  · have e : dirPt τ ((t : ℂ) • z) = t • dirPt τ z := by
      unfold dirPt
      rw [Pi.single_smul]
      rfl
    funext w
    rw [Pi.smul_apply, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
      LinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
      have h1 := omO_self h (S := S) (T := T) (u + v)
      simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
      linarith
    rw [hE, hE, hE, hE, heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota T S)
      (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) sk f hs]

theorem om_cplx (hθ : IsInfFam θ) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (τ τ' : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omO S T (dirPt τ (cplxO (sS τ) (sT τ) z)) (dirPt τ' (cplxO (sS τ') (sT τ') z')) =
      omO S T (dirPt τ z) (dirPt τ' z') ∧
    omO S T (dirPt τ (cplxO (sS τ) (sT τ) z)) (dirPt τ' z') =
      -omO S T (dirPt τ z) (dirPt τ' (cplxO (sS τ') (sT τ') z')) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
    have h1 := omO_self h (S := S) (T := T) (u + v)
    simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
    linarith
  have key := fun τ => GlobalTheory.CartanTrace.cplxO_pos T.rank S.rank (gramAt D S τ) (sS τ) (gramAt D T τ) (sT τ)
    (tauE D τ D.host.xi0) (GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero τ) (xi_zero_im_pos D τ) (hS τ) (hT τ)
  have hom : ∀ x y : RW T S, omO S T x y = ∑ τ, formAt S T τ (x τ) (y τ) := fun _ _ => rfl
  have hJ : ∀ τ z, dirPt τ (cplxO (sS τ) (sT τ) z) = GlobalTheory.OrientedRealForm.jO S T sS sT (dirPt τ z) := by
    intro τ z
    funext ρ
    show _ = cplxO (sS ρ) (sT ρ) (dirPt τ z ρ)
    unfold dirPt
    by_cases e : ρ = τ
    · subst e
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e]
      simp [cplxO]
  have hJJ : ∀ v, GlobalTheory.OrientedRealForm.jO S T sS sT (GlobalTheory.OrientedRealForm.jO S T sS sT v) = -v := fun v => by
    funext τ
    exact (key τ).2.1 (v τ)
  have hsym : ∀ x y, omO S T x (GlobalTheory.OrientedRealForm.jO S T sS sT y) =
      omO S T y (GlobalTheory.OrientedRealForm.jO S T sS sT x) := fun x y => by
    rw [hom, hom]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine (GlobalTheory.OrientedRealForm.formAt_eq S T τ _ _).trans
      (Eq.trans ?_ (GlobalTheory.OrientedRealForm.formAt_eq S T τ _ _).symm)
    exact congrArg (2 * ·) ((key τ).2.2.1 (x τ) (y τ))
  rw [hJ, hJ]
  constructor
  · rw [hsym, hJJ, map_neg, ← sk]
  · rw [sk, hsym]

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
  (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)

theorem aPlus_eq (f : WO S T → ℂ) : aPlus (heisO ψ S T) θ τ J z f =
    ((fockScale D τ : ℂ)⁻¹) • (Datum.dRho (heisO ψ S T) θ τ z f + (-I) • Datum.dRho (heisO ψ S T) θ τ (J z) f) := by
  rw [aPlus, crea, neg_smul, sub_eq_add_neg]

include hψ hθ

theorem aPlus_th {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (aPlus (heisO ψ S T) θ τ J z f) := by
  rw [aPlus_eq]
  exact theta_smul _ (theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf)))

theorem aPlus_add {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    aPlus (heisO ψ S T) θ τ J z (f + f') = aPlus (heisO ψ S T) θ τ J z f + aPlus (heisO ψ S T) θ τ J z f' := by
  simp only [aPlus_eq, fun z => (dRho_laws hψ hθ hf τ z).1 f' hf']
  module

theorem aPlus_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (a • f) = a • aPlus (heisO ψ S T) θ τ J z f := by
  simp only [aPlus_eq, fun z => (dRho_laws hψ hθ hf τ z).2.1 a]
  module

theorem aPlus_comm {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' (aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => eq_add_of_sub_eq ((dRho_laws hψ hθ hf τ z).2.2.2.2 τ' z')
  obtain ⟨h1, h2⟩ := om_cplx hθ hS hT τ τ' z z'
  rw [aPlus_eq τ' _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _ _), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq]
  rw [hc τ z τ' z', hc τ z τ' (cplxO (sS τ') (sT τ') z'), hc τ (cplxO (sS τ) (sT τ) z) τ' z',
    hc τ (cplxO (sS τ) (sT τ) z) τ' (cplxO (sS τ') (sT τ') z'), h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

end GlobalTheory.FockSubst
