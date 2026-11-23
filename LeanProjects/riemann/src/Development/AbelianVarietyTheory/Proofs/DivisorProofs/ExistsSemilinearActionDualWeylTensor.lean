import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemilinTransport

open MvPolynomial

theorem map_mem {R : Type} [CommRing R] (σ : R →+* R) {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    map σ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
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
        map σ (Formalism.GradedWeylDivisibility.colAddGen R l j g) = Formalism.GradedWeylDivisibility.colAddGen R l j (map σ g) := by
      intro g
      unfold Formalism.GradedWeylDivisibility.colAddGen
      rw [aeval_eq_bind₁, map_bind₁]
      congr 2
      funext v
      split_ifs <;> simp
    rw [← hc, e, map_rename]

def onFactor {R : Type} [CommRing R] (σ : R →+* R) (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R r n ν →+ Formalism.GradedWeylDivisibility.dualWeyl R r n ν where
  toFun f := ⟨map σ (f : MvPolynomial (Fin r × Fin n) R), map_mem σ f.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

theorem onFactor_smul {R : Type} [CommRing R] (σ : R →+* R) (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : onFactor σ r n ν (c • f) = σ c • onFactor σ r n ν f := by
  ext1
  simp [onFactor, smul_eq_C_mul]

def Tw {R : Type} [CommRing R] (_σ : R →+* R) (M : Type) : Type := M

instance {R : Type} [CommRing R] (σ : R →+* R) (M : Type) [AddCommGroup M] : AddCommGroup (Tw σ M) :=
  inferInstanceAs (AddCommGroup M)

instance {R : Type} [CommRing R] (σ : R →+* R) (M : Type) [AddCommGroup M] [Module R M] :
    Module R (Tw σ M) :=
  Module.compHom M σ

variable {R : Type} [CommRing R] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

def mlin (σ : R →+* R) :
    MultilinearMap R (fun τ : ι => Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ)))
      (Tw σ (NablaT R N mu)) where
  toFun x := (PiTensorProduct.tprod R (fun τ => onFactor σ N N _ (x τ)) : NablaT R N mu)
  map_update_add' := by
    intro _ x i a b
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, map_add]
    exact (PiTensorProduct.tprod R).map_update_add _ i _ _
  map_update_smul' := by
    intro _ x i c a
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, onFactor_smul]
    exact (PiTensorProduct.tprod R).map_update_smul _ i _ _

def semi (σ : R →+* R) : NablaT R N mu →+ NablaT R N mu :=
  (PiTensorProduct.lift (mlin N mu σ)).toAddMonoidHom

theorem semi_tprod (σ : R →+* R) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    semi N mu σ (PiTensorProduct.tprod R x) = PiTensorProduct.tprod R (fun τ => onFactor σ N N _ (x τ)) :=
  by
    show (PiTensorProduct.lift (mlin N mu σ)) (PiTensorProduct.tprod R x) = _
    rw [PiTensorProduct.lift.tprod]; rfl

theorem semi_smul (σ : R →+* R) (c : R) (y : NablaT R N mu) :
    semi N mu σ (c • y) = σ c • semi N mu σ y :=
  (PiTensorProduct.lift (mlin N mu σ)).map_smul c y

end GlobalTheory.SemilinTransport

namespace GlobalTheory.SemilinTransport

open MvPolynomial

variable {R : Type} [CommRing R] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

theorem semi_left_inv (g : R ≃+* R) (y : NablaT R N mu) :
    semi N mu (g.symm : R →+* R) (semi N mu (g : R →+* R) y) = y := by
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

theorem fix_inv (g : R ≃+* R) (u : GL (Fin N) R)
    (hu : ∀ a b, g ((u : Matrix (Fin N) (Fin N) R) a b) = (u : Matrix (Fin N) (Fin N) R) a b) (a b : Fin N) :
    g (((u⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b) = ((u⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b := by
  have hU : Units.map ((g : R →+* R).mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R).toMonoidHom u = u :=
    Units.ext (by ext i j; simp [hu])
  have h2 : Units.map ((g : R →+* R).mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R).toMonoidHom u⁻¹ = u⁻¹ := by
    rw [map_inv, hU]
  have := congrArg (fun w : GL (Fin N) R => (w : Matrix (Fin N) (Fin N) R) a b) h2
  simpa using this

theorem onFactor_rep (g : R ≃+* R) (u : GL (Fin N) R)
    (hu : ∀ a b, g ((u : Matrix (Fin N) (Fin N) R) a b) = (u : Matrix (Fin N) (Fin N) R) a b) (ν : Fin N → ℕ)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R N N ν) :
    onFactor (g : R →+* R) N N ν (Formalism.UG.dualWeylRep R N N ν u f) =
      Formalism.UG.dualWeylRep R N N ν u (onFactor (g : R →+* R) N N ν f) := by
  ext1
  simp only [onFactor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.dualWeylRep_apply]
  unfold Formalism.UG.dwAct Formalism.GradedWeylDivisibility.rowAct
  rw [aeval_eq_bind₁, map_bind₁]
  congr 2
  funext v
  simp only [map_sum, map_mul, map_C, map_X]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := fix_inv N g u hu v.1 b
  simp only [RingHom.coe_coe] at this ⊢
  rw [this]

theorem grp_tprod [DecidableEq ι] (h : ι → GL (Fin N) R)
    (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    grp R N mu h (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun τ => Formalism.UG.dualWeylRep R N N _ (h τ) (x τ)) := by
  simp [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

theorem semi_grp [DecidableEq ι] (g : R ≃+* R) (h : ι → GL (Fin N) R)
    (hh : ∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b)
    (y : NablaT R N mu) :
    semi N mu (g : R →+* R) (grp R N mu h y) = grp R N mu h (semi N mu (g : R →+* R) y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, semi_smul, semi_smul, map_smul, grp_tprod, semi_tprod, semi_tprod, grp_tprod]
    congr 2
    funext τ
    exact onFactor_rep N g (h τ) (hh τ) _ (x τ)
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end GlobalTheory.SemilinTransport

namespace GlobalTheory

open GlobalTheory.SemilinTransport

theorem semilinear_transport : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ)
    (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧
    ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) →
      ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  intro R _ ι _ _ N mu g
  refine ⟨semi N mu (g : R →+* R), fun y y' e => ?_, fun c x => semi_smul N mu _ c x,
    fun h hh x => semi_grp N mu g h hh x⟩
  rw [← semi_left_inv N mu g y, ← semi_left_inv N mu g y', e]

end GlobalTheory
