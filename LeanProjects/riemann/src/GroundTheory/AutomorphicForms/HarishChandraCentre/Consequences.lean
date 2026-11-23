import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable def casimirGL2 : U 2 :=
  (1 / 2 : ℂ) • ((e (0, 0) - e (1, 1)) * (e (0, 0) - e (1, 1))) + e (0, 1) * e (1, 0) +
    e (1, 0) * e (0, 1)

theorem rep_center_apply_of_highestWeight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    (z : Subalgebra.center ℂ (U n)) :
    φ z v = eval (lam + rhoVec n) (harishChandraHom z) • v := by
  rw [rep_apply_of_highestWeight φ lam hup hH
    (commute_e_diag_of_mem (mem_centralizerT_of_mem_center z.2)), eval_harishChandraHom,
    add_sub_cancel_right]

def conjAlgHom (g : (gl n)ˣ) : gl n →ₐ[ℂ] gl n where
  toFun X := (g : gl n) * X * ↑g⁻¹
  map_one' := by simp
  map_mul' X Y := by
    simp only [mul_assoc]; rw [← mul_assoc (↑g⁻¹ : gl n) (g : gl n), Units.inv_mul, one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      Units.mul_inv]

noncomputable def conjU (g : (gl n)ˣ) : U n →ₐ[ℂ] U n :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (conjAlgHom g).toLieHom)

theorem conjU_ι (g : (gl n)ˣ) (X : gl n) :
    conjU g (UniversalEnvelopingAlgebra.ι ℂ X) = UniversalEnvelopingAlgebra.ι ℂ ((g : gl n) * X * ↑g⁻¹) := by
  simp [conjU, conjAlgHom]

theorem conjU_conjU_inv (g : (gl n)ˣ) (u : U n) : conjU g (conjU g⁻¹ u) = u := by
  have : (conjU g).comp (conjU g⁻¹) = AlgHom.id ℂ (U n) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext X
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply,
      conjU_ι, AlgHom.id_apply, inv_inv]
    congr 1
    simp [mul_assoc]
  exact congrArg (fun F : U n →ₐ[ℂ] U n => F u) this

theorem conjU_mem_center {g : (gl n)ˣ} {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    conjU g z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro u
  rw [← conjU_conjU_inv g u, ← map_mul, ← map_mul, hz]

theorem rep_center_apply_mem_span_of_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) (g : (gl n)ˣ) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (conjU g (e a)) v = 0)
    (hH : ∀ k, φ (conjU g (e (k, k))) v = lam k • v) {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    ∃ c : ℂ, φ z v = c • v := by
  have hz' : conjU g⁻¹ z ∈ Subalgebra.center ℂ (U n) := conjU_mem_center hz
  refine ⟨eval (lam + rhoVec n) (harishChandraHom ⟨_, hz'⟩), ?_⟩
  have := rep_center_apply_of_highestWeight (φ.comp (conjU g)) lam hup hH ⟨_, hz'⟩
  simpa [conjU_conjU_inv] using this

end GroundTheory.Automorphic.HarishChandra
