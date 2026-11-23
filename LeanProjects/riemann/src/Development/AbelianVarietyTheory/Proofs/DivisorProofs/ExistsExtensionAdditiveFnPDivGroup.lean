import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounitalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoactionEqAddOfPrimitiveStatement

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_res_eq_of_transl_eq_add {b : G.A 1} (hb : cobOne R (G.A 1) b = 0) (n : ℕ)
    (x : G.A (n + 1)) (hx : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ∃ y : G.A (n + 2), G.transl (n + 1) y = y ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b ∧ G.res (n + 1) y = x := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.transl_coaction_free_coassoc_counital G (n + 1)
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_coaction_eq_add_of_primitive (G.transl (n + 1)) h1 h2 h3 b hb
  have hr : G.transl n (G.res (n + 1) x') = G.res (n + 1) x' ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [transl_res, hx', map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n (G.res (n + 1) x' - x) (by
    rw [map_sub, hr, hx, sub_tmul]
    abel)
  obtain ⟨e', rfl⟩ := G.res_surjective n e
  refine ⟨x' - G.mulP (n + 1) e', ?_, ?_⟩
  · rw [map_sub, hx', transl_mulP, sub_tmul]
    abel
  · rw [map_sub, res_mulP, ← mulP_res, he, sub_sub_cancel]

theorem exists_funs_transl_eq_add {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (b : G.A 1) (hb : cobOne R (G.A 1) b = 0) :
    ∃ B : G.funs, B.1 1 = b ∧
      ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  choose f hf hres using G.exists_res_eq_of_transl_eq_add hb
  have h0 : G.transl 0 b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    have h : (G.resOne 0 : G.A 1 →ₗ[R] G.A 1) = LinearMap.id := rfl
    rw [transl_apply, h, LinearMap.lTensor_id, LinearMap.id_apply]
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb
    exact hb
  let s : ∀ n, {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b} := fun n =>
    Nat.rec (motive := fun n => {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b})
      ⟨b, h0⟩ (fun n x => ⟨f n x.1 x.2, hf n x.1 x.2⟩) n
  refine ⟨⟨fun n => Nat.casesOn (motive := fun n => G.A n) n (G.res 0 b) fun n => (s n).1, ?_⟩,
    rfl, fun n => (s n).2⟩
  rintro (_ | n)
  · rfl
  · exact hres n (s n).1 (s n).2

end PDivGroup

end GlobalTheory
