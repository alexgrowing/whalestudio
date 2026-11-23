import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_map_eq_H {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ * H.map τ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem gramOn_det_totallyPositive_of_posDef {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E)
    (hH : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q)
    (V : Submodule E (Fin n → E)) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det ≠ 0 ∧
      ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det = r := by
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det := by
    intro τ
    obtain ⟨Q, hQ, hHQ⟩ := hH τ
    rw [RingHom.map_det]
    have e1 : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ := rfl
    have e2 : cT (starRingEnd ℂ) Q = Qᴴ := by
      ext i j; simp [cT, Matrix.conjTranspose_apply]
    set A : Matrix (Fin n) (Fin (Module.finrank E V)) ℂ :=
      Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) with hA
    have e3 : Aᴴ * (Qᴴ * Q) * A = (Q * A)ᴴ * (Q * A) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, gramOn_map_eq_H, ← hA, hHQ, e2, e3]
    have hQi : Function.Injective Q.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hQ
    have hinj : Function.Injective (Q * A).mulVec := by
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact gramOn_basis_mulVec_injective V τ (hQi hvw)
    exact (Matrix.PosDef.conjTranspose_mul_self _ hinj).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

theorem refSign_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  intro E _ _ _ hU S hS n γ₀ _ H₀ _ _ _ hpos P₁ _ _
  obtain ⟨hd0, hdpos⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine Eq.trans ?_ (GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one E hU S hS _ hd0 hdpos)
  apply finprod_mem_congr rfl
  intro w _
  split_ifs with hw
  · rfl
  · unfold sgnOn
    rw [aeval_map_mat]
    exact GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁)

end GlobalTheory.UnitaryClasses
