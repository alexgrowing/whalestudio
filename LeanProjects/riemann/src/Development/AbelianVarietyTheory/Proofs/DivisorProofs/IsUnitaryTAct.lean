import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

lemma star_adP_Eab {R S : ℕ} (a b : Ix R S) (y x : NC R S) :
    (starRingEnd ℂ) (adP (Eab a b) y x) = adP (Eab b a) x y := by
  simp only [adP, Eab, Matrix.single_apply, map_sub, map_mul, apply_ite (starRingEnd ℂ), map_one, map_zero]
  congr 2
  · simp only [and_comm]
  · simp only [eq_comm]
  · simp only [eq_comm]
  · simp only [and_comm]

lemma sum_update_swap {ι α M : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [AddCommMonoid M] (i : ι)
    (F : (ι → α) → (ι → α) → M) :
    ∑ g : ι → α, ∑ x, F g (Function.update g i x) = ∑ g : ι → α, ∑ x, F (Function.update g i x) g := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have hinv : Function.Involutive (fun p : (ι → α) × α => (Function.update p.1 i p.2, p.1 i)) := by
    intro p; simp
  refine Fintype.sum_equiv hinv.toPerm _ _ fun p => ?_
  simp [Function.Involutive.toPerm]

theorem isUnitary_tAct (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (h : IsUnitary actW B) : IsUnitary (tAct k actW) (formT k B) := by
  obtain ⟨hs, hp, ha⟩ := h
  refine ⟨fun Ψ Φ => ?_, fun Ψ hΨ => ?_, fun a b hab Ψ Φ => ?_⟩
  · simp only [formT_apply, star_sum, hs]
  · rw [formT_apply, Complex.re_sum]
    obtain ⟨g, hg⟩ := Function.ne_iff.1 hΨ
    refine Finset.sum_pos' (fun g' _ => ?_) ⟨g, Finset.mem_univ _, hp _ hg⟩
    by_cases h0 : Ψ g' = 0
    · simp [h0]
    · exact (hp _ h0).le
  · simp only [formT_apply, tAct_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib, ha a b hab, map_sum,
      LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, star_adP_Eab, RingHom.id_apply]
    congr 1
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin k → NC R S)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := sum_update_swap i (fun g g' : Fin k → NC R S => adP (Eab b a) (g' i) (g i) * B (Ψ g') (Φ g))
    simpa only [Function.update_self] using this

end GlobalTheory.SteepMult

end
