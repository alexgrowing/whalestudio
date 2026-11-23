import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.SingleBlockJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviEmb_oneBlock (N : ℕ) (g : Levi k fun _ : Fin 1 => Fin N) :
    leviEmb k (GlobalTheory.JacTensor.oneBlock N) g = g 0 := by
  ext i j
  exact leviEmb_apply_same k (GlobalTheory.JacTensor.oneBlock N) g 0 i j

theorem deltaHalf_one (N : ℕ) (g : Levi k fun _ : Fin 1 => Fin N) :
    deltaHalf k (fun _ : Fin 1 => Fin N) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hm : modExp (fun _ : Fin 1 => Fin N) a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro c hc
      exact absurd (Finset.mem_filter.1 hc).2 (by rw [Subsingleton.elim c a]; exact lt_irrefl a)
    · intro c hc
      exact absurd (Finset.mem_filter.1 hc).2 (by rw [Subsingleton.elim c a]; exact lt_irrefl a)
  rw [hm]
  simp

theorem eq_one_of_mem_unipRad_oneBlock {N : ℕ} (e : (Σ _ : Fin 1, Fin N) ≃ Fin N) {g : GL (Fin N) k}
    (hg : g ∈ unipRad k e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  obtain rfl : a = b := Subsingleton.elim a b
  rw [h2 a i j]
  simp [Matrix.one_apply, e.injective.eq_iff]

theorem twKer_eq_bot {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (e : (Σ _ : Fin 1, Fin N) ≃ Fin N)
    (π : Representation ℂ (GL (Fin N) k) V) : twKer π (unipRad k e) 1 = ⊥ := by
  refine (Submodule.span_eq_bot).2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [eq_one_of_mem_unipRad_oneBlock e n.2]
  simp

def toJac {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (π : Representation ℂ (GL (Fin N) k) V) :
    (piTensor fun _ : Fin 1 => π).IntertwiningMap (jac (GlobalTheory.JacTensor.oneBlock N) π) where
  toLinearMap := Submodule.mkQ _ ∘ₗ (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1)).toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [LinearMap.comp_apply, map_smul, piTensor_tprod, LinearEquiv.coe_coe,
        PiTensorProduct.subsingletonEquiv_apply_tprod, Submodule.mkQ_apply]
      rw [jac_mk, deltaHalf_one, leviEmb_oneBlock]
      simp [Subsingleton.elim (0 : Fin 1) 0]
    | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]

theorem toJac_injective {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (π : Representation ℂ (GL (Fin N) k) V) :
    Function.Injective (toJac N π) := by
  intro x y h
  have h' : (Submodule.mkQ (twKer π (unipRad k (GlobalTheory.JacTensor.oneBlock N)) 1))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1) x) =
      (Submodule.mkQ (twKer π (unipRad k (GlobalTheory.JacTensor.oneBlock N)) 1))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1) y) := h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, twKer_eq_bot,
    Submodule.mem_bot, sub_eq_zero] at h'
  exact (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1)).injective h'

end GlobalTheory.SingleBlockJac

theorem GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (jac e π) := by
  intro k _ _ _ _ N V _ _ π e
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin 1) (Fin N) (fun _ => Fin N)
    (GlobalTheory.JacTensor.oneBlock N) e V).2 π
  exact IsSubquotient.of_injective ((φ.toIntertwiningMap).comp (GlobalTheory.SingleBlockJac.toJac N π))
    (φ.toLinearEquiv.injective.comp (GlobalTheory.SingleBlockJac.toJac_injective N π))
