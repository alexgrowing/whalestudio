import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_idem_le_of_embReg : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V]
    [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ,
    (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧
      finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  intro K Γ V _ _ _ _ _ _ ρ H n hE a ha hidem
  obtain ⟨j, hj, hjρ⟩ := hE
  classical
  let ψ := MonoidAlgebra.mapDomainAlgHom K K H.subtype
  have hψinj : Function.Injective ψ := MonoidAlgebra.mapDomain_injective Subtype.val_injective
  let a' : MonoidAlgebra K H :=
    MonoidAlgebra.ofCoeff (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn)
  have hψa : ψ a' = a := by
    apply MonoidAlgebra.coeff_injective
    show Finsupp.mapDomain Subtype.val (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn) = a.coeff
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro g hg
    exact ⟨⟨g, ha g (by simpa using hg)⟩, rfl⟩
  have hidem' : a' * a' = a' := hψinj (by rw [map_mul, hψa, hidem])
  have hc1 : a'.coeff 1 = a.coeff 1 := rfl
  have key : ∀ (b : MonoidAlgebra K H) (v : V) (i : Fin n), j (ρ.asAlgebraHom (ψ b) v) i = b * j v i := by
    intro b
    induction b using MonoidAlgebra.induction_on with
    | of h =>
      intro v i
      have : ψ (MonoidAlgebra.of K H h) = MonoidAlgebra.of K Γ (h : Γ) := by
        simp [ψ]
      rw [this, Representation.asAlgebraHom_of, hjρ h v i]
      rfl
    | add b c hb hc => intro v i; simp [map_add, LinearMap.add_apply, hb, hc, add_mul]
    | smul r b hb => intro v i; simp [map_smul, LinearMap.smul_apply, hb, smul_mul_assoc]
  refine ⟨finrank K (LinearMap.range (LinearMap.mulLeft K a')), ?_, ?_⟩
  · rw [GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra K H a' hidem', hc1]
  · let R := LinearMap.range (LinearMap.mulLeft K a')
    let g : LinearMap.range (ρ.asAlgebraHom a) →ₗ[K] (Fin n → R) :=
      LinearMap.pi fun i => LinearMap.codRestrict R
        ((LinearMap.proj i).comp (j.comp (LinearMap.range (ρ.asAlgebraHom a)).subtype)) (by
          rintro ⟨x, v, rfl⟩
          refine ⟨j v i, ?_⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply]
          rw [← hψa, key])
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.val_injective
      apply hj
      funext i
      have := congrArg (fun f => ((f i : R) : MonoidAlgebra K H)) hxy
      simpa [g] using this
    have := LinearMap.finrank_le_finrank_of_injective hg
    rw [Module.finrank_pi_fintype] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

end GlobalTheory.BadCount
