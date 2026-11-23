import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

noncomputable section
namespace GlobalTheory.DualTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]

def dualEquiv : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₗ[ℚ_[l]] Module.Dual ℚ_[l] V :=
  (Module.finBasis ℚ_[l] V).dualBasis.equivFun.symm

theorem dualEquiv_basis (z : Fin (finrank ℚ_[l] V) → ℚ_[l]) (i : Fin (finrank ℚ_[l] V)) :
    dualEquiv z (Module.finBasis ℚ_[l] V i) = z i := by
  simp [dualEquiv, Basis.equivFun_symm_apply, Finset.sum_apply, Basis.dualBasis_apply_self, Finsupp.single_apply]

theorem dualEquiv_symm_apply (f : Module.Dual ℚ_[l] V) (i : Fin (finrank ℚ_[l] V)) :
    (dualEquiv (V := V)).symm f i = f (Module.finBasis ℚ_[l] V i) := by
  conv_rhs => rw [← (dualEquiv (V := V)).apply_symm_apply f]
  rw [dualEquiv_basis]

def chiS (g : ↥(GK K)) : ℚ_[l] := ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])

theorem chiS_mul (g h : ↥(GK K)) : chiS P K (g * h) = chiS P K g * chiS P K h := by
  simp [chiS]

theorem chiS_one : chiS P K 1 = 1 := by simp [chiS]

def dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) :
    (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun y := chiS P K g • (dualEquiv (V := V)).symm ((dualEquiv y).comp (ρ g⁻¹))
  map_add' y z := by simp [LinearMap.add_comp, smul_add]
  map_smul' c y := by simp [LinearMap.smul_comp, smul_comm c]

theorem dualEquiv_dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (y) :
    dualEquiv (dualOp P K ρ g y) = chiS P K g • (dualEquiv y).comp (ρ g⁻¹) := by
  simp [dualOp]

def dualRep (ρ : Representation ℚ_[l] ↥(GK K) V) :
    Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun g := dualOp P K ρ g
  map_one' := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [dualEquiv_dualOp]
    simp [chiS_one, Module.End.one_eq_id]
  map_mul' g h := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [Module.End.mul_apply, dualEquiv_dualOp, dualEquiv_dualOp, dualEquiv_dualOp, chiS_mul,
      mul_inv_rev, map_mul, Module.End.mul_eq_comp, LinearMap.smul_comp, smul_smul, LinearMap.comp_assoc]

def dualPair : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l] :=
  (dualEquiv (V := V)).toLinearMap.flip

theorem dualPair_apply (x : V) (y : Fin (finrank ℚ_[l] V) → ℚ_[l]) : dualPair x y = dualEquiv y x := rfl

end GlobalTheory.DualTwist

namespace GlobalTheory.DualTwist
variable {l : ℕ} [Fact l.Prime]

theorem chiS_eq (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    chiS P K g = (P.χQ (g : GQ l) : ℚ_[l]) := by
  simp [chiS, cycLL, P.PD_χ]

theorem chiS_cont (P : LocPrime l) (K : FinExt l) : Continuous (chiS P K) := by
  have h : chiS P K = fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) := funext (chiS_eq P K)
  rw [h]
  exact (GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val

theorem exists_dual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  refine ⟨dualRep P K ρ, dualPair, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply continuous_pi
    intro i
    have h : (fun g : ↥(GK K) => dualRep P K ρ g y i) =
        fun g => chiS P K g * dualEquiv y (ρ g⁻¹ (Module.finBasis ℚ_[l] V i)) := by
      funext g
      change dualOp P K ρ g y i = _
      simp [dualOp, dualEquiv_symm_apply]
    rw [h]
    have hy : Continuous (dualEquiv (V := V) y) :=
      IsModuleTopology.continuous_of_linearMap (dualEquiv (V := V) y)
    exact (chiS_cont P K).mul (hy.comp ((hc _).comp continuous_inv))
  · intro g x y
    change dualEquiv (dualOp P K ρ g y) (ρ g x) = chiS P K g * dualEquiv y x
    rw [dualEquiv_dualOp, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, smul_eq_mul]
  · intro x hx
    apply (Module.finBasis ℚ_[l] V).forall_coord_eq_zero_iff.mp
    intro i
    have := hx ((dualEquiv (V := V)).symm ((Module.finBasis ℚ_[l] V).coord i))
    rwa [dualPair_apply, LinearEquiv.apply_symm_apply] at this
  · intro y hy
    funext i
    exact (dualEquiv_basis y i).symm.trans (hy _)
  · simp

end GlobalTheory.DualTwist
