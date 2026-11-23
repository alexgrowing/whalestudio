import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversedStatement
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace GlobalTheory.CompactHowe.Lift

open MvPolynomial

theorem map_star_subst2 {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (subst2 A B P) =
      subst2 (A.map star) (B.map star) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have key : (MvPolynomial.map (starRingEnd ℂ)).comp (subst2 A B).toRingHom =
      (subst2 (A.map star) (B.map star)).toRingHom.comp (MvPolynomial.map (starRingEnd ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun p => ?_)
    · simp
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, subst2_X,
        map_sum, map_mul, map_C, Matrix.map_apply]
      rfl
  exact congrArg (fun f => f P) key

theorem map_star_map_star_poly {N n : ℕ} (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => by simp
  rw [this, MvPolynomial.map_id]

theorem map_star_smul {N n : ℕ} (c : ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (c • P) = star c • MvPolynomial.map (starRingEnd ℂ) P := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C]
  rfl

end GlobalTheory.CompactHowe.Lift

namespace GlobalTheory.CompactHowe

open Contraction Lift

theorem exists_local_lift : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) → (∀ b, Λ' b = (x₁ : ℝ) + ν b) → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) σ → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) σ Λ ⊤ → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N)) σ' → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H →ₗ[ℂ] H', I ≠ 0 ∧ ∀ h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N), ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • GlobalTheory.CompactHowe.subst2 h (g⁻¹)ᵀ P) (σ g v) = σ' h (I P v) := by
  intro N n hn ν x₁ x₃ Λ Λ' H _ _ _ σ H' _ _ _ σ' hν hν0 hΛ hΛ' hσ hK hσ' hK'
  obtain ⟨hτ, hτK⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed n Λ 0 H σ hσ hK
  obtain ⟨hτ', hτK'⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed N Λ' 0 H' σ' hσ' hK'
  obtain ⟨I₀, hI₀0, hI₀⟩ := GlobalTheory.T.exists_local_howe_contraction_compact_unitary N n hn ν x₁ x₃ (fun a => ((0 : ℤ) : ℝ) - Λ (Fin.rev a))
    (fun b => ((0 : ℤ) : ℝ) - Λ' (Fin.rev b)) H (fun g => g.det ^ (0 : ℤ) • σ (g.map star)) H'
    (fun g => g.det ^ (0 : ℤ) • σ' (g.map star)) hν hν0
    (fun a => by simp only [hΛ, Int.cast_zero]; ring) (fun b => by simp only [hΛ', Int.cast_zero]; ring)
    hτ hτK hτ' hτK'
  let cj : MvPolynomial (Fin N × Fin n) ℂ →+* MvPolynomial (Fin N × Fin n) ℂ :=
    MvPolynomial.map (starRingEnd ℂ)
  refine ⟨{ toFun := fun P => LinearMap.adjoint (I₀ (cj P)),
            map_add' := fun P Q => by simp only [map_add]
            map_smul' := fun c P => by
              simp only [cj, map_star_smul, map_smul, LinearEquiv.map_smulₛₗ, RingHom.id_apply]
              simp }, fun h0 => hI₀0 ?_, fun h hh g hg P v => ?_⟩
  · refine LinearMap.ext fun P => ?_
    have := congrArg (fun f => f (cj P)) h0
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, cj, map_star_map_star_poly] at this
    simpa using this
  · have hQ : cj ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) =
        ((h.map star).det ^ x₁ * (g.map star).det ^ x₃) • subst2 (h.map star) ((g.map star)⁻¹)ᵀ (cj P) := by
      simp only [cj]
      rw [map_star_smul, map_star_subst2, Contraction.inv_transpose hg,
        Contraction.inv_transpose (map_star_mem hg)]
      simp only [Contraction.det_map_star, star_mul', star_zpow₀]
    have key := hI₀ (h.map star) (map_star_mem hh) (g.map star) (map_star_mem hg) (cj P)
    simp only [zpow_zero, one_smul, map_star_map_star] at key
    show LinearMap.adjoint (I₀ (cj _)) (σ g v) = σ' h (LinearMap.adjoint (I₀ (cj P)) v)
    rw [hQ]
    refine ext_inner_left ℂ fun w => ?_
    obtain ⟨u, rfl⟩ : ∃ u, σ' h u = w := by
      refine ⟨σ' hᴴ w, ?_⟩
      have := hσ'.1.2 h hh _ (conjTranspose_mem hh)
      rw [mul_eq_one_comm.1 ((mem_iff h).1 hh), hσ'.1.1] at this
      simpa using (congrArg (fun f => f w) this).symm
    have iso1 : ∀ a b : H, inner ℂ (σ g a) (σ g b) = inner ℂ a b := fun a b =>
      (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map a b
    have iso2 : ∀ a b : H', inner ℂ (σ' h a) (σ' h b) = inner ℂ a b := fun a b =>
      (LinearIsometry.mk (σ' h : H' →ₗ[ℂ] H') (hσ'.2.1 h hh)).inner_map_map a b
    rw [LinearMap.adjoint_inner_right, key u, iso1, iso2, LinearMap.adjoint_inner_right]

end GlobalTheory.CompactHowe
