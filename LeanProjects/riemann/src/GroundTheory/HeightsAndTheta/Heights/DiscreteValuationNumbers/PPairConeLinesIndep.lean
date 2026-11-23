import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem PairConeLinesIndep.formMatrix_isUnit {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {N : ℕ}
    (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E) (hψ : LinearIndependent Ω ψ) :
    IsUnit (Matrix.of fun i j => ψ i (e j)) := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have h := hψ.map' e.dualBasis.equivFun.toLinearMap e.dualBasis.equivFun.ker
  have hrows : (Matrix.of fun i j => ψ i (e j)).row = ⇑e.dualBasis.equivFun ∘ ψ := by
    funext i
    funext j
    simp [Matrix.row, Module.Basis.equivFun_apply]
  rw [hrows]
  exact h

theorem PairConeLinesIndep.linearChange_indep {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {N : ℕ}
    (P : Matrix (Fin N) (Fin N) Ω) (hP : IsUnit P) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (P i j)) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  let f : Fin N → MvPolynomial (Fin N) Ω := fun i => ∑ j, X j * C (P i j)
  let g : Fin N → MvPolynomial (Fin N) Ω := fun j => ∑ k, X k * C (P⁻¹ j k)
  have hgf : (fun i => aeval g (f i)) = X := by
    funext i
    simp only [f, g, map_sum, map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq]
    calc ∑ j, (∑ k, X k * C (P⁻¹ j k)) * C (P i j)
        = ∑ k, X k * C ((P * P⁻¹) i k) := by
          simp_rw [Finset.sum_mul, Matrix.mul_apply, map_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]
          ring
      _ = X i := by
          rw [Matrix.mul_nonsing_inv _ hdet]
          simp [Matrix.one_apply]
  have hf : AlgebraicIndependent Ω f := by
    apply AlgebraicIndependent.of_aeval (x := g)
    rw [hgf]
    exact algebraicIndependent_X _ _
  have h := ht.aeval_of_algebraicIndependent hf
  convert h using 1
  funext i
  simp [f, map_sum, aeval_X]

theorem PairConeLinesIndep.proof : PairConeLinesIndep.Statement := by
  intro Ω _ Φ _ _ K N E _ _ e ψ hψ t ht g hg
  have hw : AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (ψ i (e j))) :=
    PairConeLinesIndep.linearChange_indep (Matrix.of fun i j => ψ i (e j))
      (PairConeLinesIndep.formMatrix_isUnit e ψ hψ) t ht
  let T : K → MvPolynomial (Option (Option K)) Φ := fun k => X (some (some k))
  let idx : Unit ⊕ K → Option (Option K) := Sum.elim (fun _ => none) (fun k => some (some k))
  have hidx : Function.Injective idx := by
    rintro (_ | a) (_ | b) h <;> simp_all [idx]
  have hvars : AlgebraicIndependent Φ (X ∘ idx : Unit ⊕ K → MvPolynomial (Option (Option K)) Φ) :=
    (algebraicIndependent_X _ _).comp idx hidx
  have hA := AlgebraicIndependent.sumElim_comp hw hvars
  have hB : AlgebraicIndependent Ω
      (Sum.elim (Sum.elim (fun i => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))))
        (fun _ : Unit => (X none : MvPolynomial (Option (Option K)) Φ))) T) := by
    have h := hA.comp ((Equiv.sumAssoc _ _ _).trans (Equiv.sumComm _ _)) (Equiv.injective _)
    convert h using 1
    funext x
    rcases x with ((i | u) | k) <;> simp [idx, T, MvPolynomial.algebraMap_eq]
  have hC := (AlgebraicIndependent.sumElim_iff.mp hB).2
  let σ : MvPolynomial (Option (Option K)) Φ →ₐ[Φ] MvPolynomial (Option (Option K)) Φ :=
    aeval fun o => Option.elim o (C g⁻¹ * X none) (fun o' => Option.elim o' 1 (fun k => X (some (some k))))
  have hfix : Algebra.adjoin Ω (Set.range T) ≤ AlgHom.equalizer (σ.restrictScalars Ω) (AlgHom.id Ω _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩
    simp [σ, T]
  let f : MvPolynomial (Option (Option K)) Φ →ₐ[Algebra.adjoin Ω (Set.range T)]
      MvPolynomial (Option (Option K)) Φ :=
    { σ.toRingHom with commutes' := fun r => hfix r.2 }
  apply AlgebraicIndependent.of_comp f
  convert hC using 1
  funext x
  rcases x with i | u
  · simp [f, σ]
  · change σ (C g * X none) = X none
    simp only [σ, map_mul, aeval_C, aeval_X, Option.elim, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, one_mul]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
