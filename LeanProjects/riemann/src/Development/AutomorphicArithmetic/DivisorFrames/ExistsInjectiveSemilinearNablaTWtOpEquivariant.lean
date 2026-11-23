import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

noncomputable section

namespace UpperTheory.RingTransport

open MvPolynomial GlobalTheory.ExpFrame

private theorem map_mem {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    map σ f ∈ Formalism.GradedWeylDivisibility.dualWeyl S r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro l j hlj
    have e := h2 l j hlj
    simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at e ⊢
    have hc : ∀ g : MvPolynomial (Fin r × Fin n) R,
        map σ (Formalism.GradedWeylDivisibility.colAddGen R l j g) = Formalism.GradedWeylDivisibility.colAddGen S l j (map σ g) := by
      intro g
      unfold Formalism.GradedWeylDivisibility.colAddGen
      rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
      congr 2
      funext v
      split_ifs <;> simp
    rw [← hc, e, map_rename]

private def onFactor {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R r n ν →+ Formalism.GradedWeylDivisibility.dualWeyl S r n ν where
  toFun f := ⟨map σ (f : MvPolynomial (Fin r × Fin n) R), map_mem σ f.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

private theorem onFactor_smul {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : onFactor σ r n ν (c • f) = σ c • onFactor σ r n ν f := by
  ext1
  simp [onFactor, smul_eq_C_mul]

private def Tw {R S : Type} [CommRing R] [CommRing S] (_σ : R →+* S) (M : Type) : Type := M

private instance instAdd {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (M : Type) [AddCommGroup M] :
    AddCommGroup (Tw σ M) :=
  inferInstanceAs (AddCommGroup M)

private instance instMod {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (M : Type) [AddCommGroup M] [Module S M] :
    Module R (Tw σ M) :=
  Module.compHom M σ

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

private def mlin (σ : R →+* S) :
    MultilinearMap R (fun τ : ι => Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ)))
      (Tw σ (NablaT S N mu)) where
  toFun x := (PiTensorProduct.tprod S (fun τ => onFactor σ N N _ (x τ)) : NablaT S N mu)
  map_update_add' := by
    intro _ x i a b
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, map_add]
    exact (PiTensorProduct.tprod S).map_update_add _ i _ _
  map_update_smul' := by
    intro _ x i c a
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, onFactor_smul]
    exact (PiTensorProduct.tprod S).map_update_smul _ i _ _

private def semi (σ : R →+* S) : NablaT R N mu →+ NablaT S N mu :=
  (PiTensorProduct.lift (mlin N mu σ)).toAddMonoidHom

private theorem semi_tprod (σ : R →+* S) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    semi N mu σ (PiTensorProduct.tprod R x) = PiTensorProduct.tprod S (fun τ => onFactor σ N N _ (x τ)) := by
  show (PiTensorProduct.lift (mlin N mu σ)) (PiTensorProduct.tprod R x) = _
  rw [PiTensorProduct.lift.tprod]; rfl

private theorem semi_smul (σ : R →+* S) (c : R) (y : NablaT R N mu) :
    semi N mu σ (c • y) = σ c • semi N mu σ y :=
  (PiTensorProduct.lift (mlin N mu σ)).map_smul c y

private theorem semi_left_inv (g : R ≃+* S) (y : NablaT R N mu) :
    semi N mu g.symm.toRingHom (semi N mu g.toRingHom y) = y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [semi_smul, semi_smul, semi_tprod, semi_tprod]
    congr 1
    · simp
    · congr 1
      funext τ
      ext1
      simp [onFactor, map_map, MvPolynomial.map_id]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem onFactor_rep (σ : R →+* S) (u : GL (Fin N) R) (ν : Fin N → ℕ)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R N N ν) :
    onFactor σ N N ν (Formalism.UG.dualWeylRep R N N ν u f) =
      Formalism.UG.dualWeylRep S N N ν (Matrix.GeneralLinearGroup.map σ u) (onFactor σ N N ν f) := by
  ext1
  simp only [onFactor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.dualWeylRep_apply]
  unfold Formalism.UG.dwAct Formalism.GradedWeylDivisibility.rowAct
  rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
  congr 2
  funext v
  simp only [map_sum, map_mul, map_C, map_X]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv]
  rfl

private theorem semi_grp [DecidableEq ι] (σ : R →+* S) (h : ι → GL (Fin N) R) (y : NablaT R N mu) :
    semi N mu σ (grp R N mu h y) =
      grp S N mu (fun τ => Matrix.GeneralLinearGroup.map σ (h τ)) (semi N mu σ y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, semi_smul, semi_smul, map_smul, GlobalTheory.SemilinTransport.grp_tprod, semi_tprod, semi_tprod,
      GlobalTheory.SemilinTransport.grp_tprod]
    congr 2
    funext τ
    exact onFactor_rep N σ (h τ) _ (x τ)
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

private theorem det_map (σ : R →+* S) (u : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map σ u) =
      Units.map (σ : R →* S) (Matrix.GeneralLinearGroup.det u) := by
  ext
  simp [RingHom.map_det]

private theorem semi_wtOp [Fintype ι] [DecidableEq ι] (sh : ι → ℤ) (σ : R →+* S) (h : ι → GL (Fin N) R) (y : NablaT R N mu) :
    semi N mu σ (wtOp R N mu sh h y) =
      wtOp S N mu sh (fun τ => Matrix.GeneralLinearGroup.map σ (h τ)) (semi N mu σ y) := by
  rw [wtOp_apply, wtOp_apply, semi_smul, semi_grp]
  congr 1
  simp only [det_map, ← map_zpow, ← map_prod]
  rfl

end UpperTheory.RingTransport

end

theorem UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant :
    ∀ (K K' : Type) [CommRing K] [CommRing K'] (io : K ≃+* K') (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
        (mu : ι → ℕ → ℕ) (sh : ι → ℤ), ∃ Φ : NablaT K n mu →+ NablaT K' n mu, Function.Injective Φ ∧ (∀ (c : K) u, Φ (c • u) = io c • Φ u) ∧
          ∀ (g : ι → GL (Fin n) K) u,
            Φ (wtOp K n mu sh g u) = wtOp K' n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (g τ)) (Φ u) := by
  intro K K' _ _ io n ι _ _ mu sh
  refine ⟨UpperTheory.RingTransport.semi n mu io.toRingHom, fun y y' e => ?_,
    fun c x => UpperTheory.RingTransport.semi_smul n mu _ c x,
    fun h x => UpperTheory.RingTransport.semi_wtOp n mu sh _ h x⟩
  rw [← UpperTheory.RingTransport.semi_left_inv n mu io y, ← UpperTheory.RingTransport.semi_left_inv n mu io y', e]
