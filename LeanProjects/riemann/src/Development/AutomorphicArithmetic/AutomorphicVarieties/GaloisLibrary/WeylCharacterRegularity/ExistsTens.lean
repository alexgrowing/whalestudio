import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.FacApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IrrSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh Topology

namespace UpperTheory.V.WeylC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_irr {D : ℕ} (hD : 0 < D) (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ) (hρ : IsReg ρ) (s : ℂ → ℂ)
    (hs : ∀ τ u, Formalism.REAL.qdet (eOf ρ τ) u = s u • 1) :
    ∃ Ξ : AlgRep E a, Ξ.d ≤ D ∧ ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = s u • 1 := by
  obtain ⟨d, A, B, ρ', h0, h1, hBA, h2, h3, h4⟩ := Weyl.irrSub _ D ρ hD
  have hρ' : IsReg ρ' := by
    have := isReg_conj hρ B A
    simpa only [← h2] using this
  refine ⟨⟨d, ρ', hρ', h0, h4⟩, h1, fun τ u => ?_⟩
  have h5 : ∀ i j, eOf ρ τ i j * A = A * eOf ρ' τ i j := fun i j => by
    have e1 := eOf_conj hρ (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have e2 := eOf_conj hρ' A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, h3] at e1 e2
    rw [← e1, e2]
  have h6 := congrArg (B * ·) (Weyl.qdetRect a D d _ _ A h5 u)
  simp only [hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hBA] at h6
  exact h6.symm

theorem exists_tens [IsTotallyComplex E] (P : Weyl.Pre a) (hP : 0 < P.d) (ν : Fin a → ℂ) (hν : P.HasWt ν) (N : ℕ) :
    ∃ Ξ : AlgRep E a, Ξ.d ≤ P.d ^ Fintype.card (E →+* ℂ) ∧
      ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = (∏ k : Fin a, (u - N - (k : ℂ) + ν k)) • 1 := by
  classical
  let e : ((E →+* ℂ) → Fin P.d) ≃ Fin (P.d ^ Fintype.card (E →+* ℂ)) := Fintype.equivFinOfCardEq (by simp)
  let r := Matrix.reindexAlgEquiv ℂ ℂ e
  let ρ : GL (Fin a) (Cinf E) →* Matrix _ _ ℂ :=
    (r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi fun τ : E →+* ℂ => fac P N τ)
  have hr := isReg_piK (fun τ : E →+* ℂ => isReg_fac P N τ)
  refine exists_irr (pow_pos hP _) ρ (fun i j => hr _ _) _ fun τ u => ?_
  have h1 : eOf ρ τ = fun i j => (r.toAlgHom.comp (intersection_update_fsHerm_neg_one τ))
      (P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := by
    funext i j
    have h2 : eOf ρ τ i j = r (eOf (fun y => piK fun t : E →+* ℂ => fac P N t y) τ i j) := rfl
    rw [h2, eOf_piK (fun τ => isReg_fac P N τ) (fun τ => map_one _), Finset.sum_eq_single τ]
    · rw [eOf_fac, if_pos rfl]; rfl
    · intro t _ ht
      rw [eOf_fac, if_neg ht, map_zero]
    · simp
  rw [h1, ← map_qdet, qdet_shift, hν, map_smul, map_one]
  simp only [sub_eq_add_neg]

end UpperTheory.V.WeylC
