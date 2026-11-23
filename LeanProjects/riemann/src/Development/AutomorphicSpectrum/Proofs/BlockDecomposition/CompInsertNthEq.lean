import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KAdjoint

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]

theorem comp_insertNth_eq {m : ℕ} (b : β → P) (s : Fin (m + 1)) (i : β) (J : Fin m → β) :
    b ∘ (s.insertNth i J : Fin (m + 1) → β) = s.insertNth (b i) (b ∘ J) := by
  funext j
  refine Fin.succAboveCases s ?_ (fun k => ?_) j
  · simp
  · simp

theorem position_sum (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) (s : Fin (m + 1)) :
    ∑ I : Fin (m + 1) → β,
        B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
      = kIp B b η (kDel T' b θ) := by
  rw [← (Fin.insertNthEquiv (fun _ => β) s).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [kIp, kDel_apply, map_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, comp_insertNth_eq, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]
  rw [← h, θ.map_insertNth]
  simp only [map_zsmul, LinearMap.smul_apply, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

theorem kIp_kD (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) :
    kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) := by
  have hs : ∀ s : Fin (m + 1), ∑ I : Fin (m + 1) → β,
      B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
        = kIp B b η (kDel T' b θ) := fun s => position_sum B b T T' h η θ s
  simp only [kIp, kD_apply, Function.comp_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp only [kIp] at hs
  rw [Finset.sum_congr rfl fun s _ => hs s]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.CompanionTheory.KAdjoint
