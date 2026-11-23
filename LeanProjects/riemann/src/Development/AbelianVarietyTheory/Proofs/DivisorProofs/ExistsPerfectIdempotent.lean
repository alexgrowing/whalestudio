import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectPartAlgHomFiniteAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectProjectionNaturalIdempotentReducedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorSquarePerfectProjectionStatement

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem exists_perfect_idempotent (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) :
    ∃ e : G ⟶ G, e ≫ e = e ∧ (∀ (n : ℕ) (a : G.A n), IsNilpotent (a - e.app n a)) ∧
      ∀ (n : ℕ) (a : G.A n), IsNilpotent (e.app n a) → e.app n a = 0 := by
  choose π hπ using fun n => GlobalTheory.T.exists_perfectPart_algHom_finiteAlgebra p k (G.A n)
  have hk : (∀ a : k, IsNilpotent (a - AlgHom.id k k a)) ∧
      ∀ a : k, ∃ b : k, AlgHom.id k k a = AlgHom.id k k b ^ p :=
    ⟨fun a => by simp, fun a => by
      obtain ⟨b, hb⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 a
      exact ⟨b, hb.symm⟩⟩
  have nat := fun n m => GlobalTheory.T.perfectProjection_natural_idempotent_reduced p k (G.A n) (G.A m) (π n) (π m) (hπ n) (hπ m)
  let b : ∀ n, G.A n →ₐc[k] G.A n := fun n => BialgHom.ofAlgHom (π n)
    (AlgHom.ext fun a => (GlobalTheory.T.perfectProjection_natural_idempotent_reduced p k (G.A n) k (π n) (AlgHom.id k k) (hπ n) hk).1
      (counitAlgHom k (G.A n)) a)
    (AlgHom.ext fun a => ((GlobalTheory.T.perfectProjection_natural_idempotent_reduced p k (G.A n) (G.A n ⊗[k] G.A n) (π n) _ (hπ n)
      (GlobalTheory.T.tensor_map_nilpotent_sub_and_pow_of_projection p k (G.A n) (π n) (hπ n))).1 (comulAlgHom k (G.A n)) a).symm)
  refine ⟨⟨b, fun n => ?_⟩, ?_, fun n a => (hπ n).1 a, fun n a => (nat n n).2.2 a⟩
  · refine BialgHom.ext fun a => ?_
    exact (nat (n + 1) n).1 (G.res n : G.A (n + 1) →ₐ[k] G.A n) a
  · exact hom_ext fun n => BialgHom.ext fun a => (nat n n).2.1 a

end GlobalTheory.PDivGroup
