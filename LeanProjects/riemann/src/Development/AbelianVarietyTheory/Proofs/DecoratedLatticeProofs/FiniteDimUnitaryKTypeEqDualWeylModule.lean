import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCTypeWConj
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.DualWeylType

open GlobalTheory.ConjugateType

theorem dual_weyl_type : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  intro k n h lam H _ _ _ σ lamH hσ hK hrho

  obtain ⟨hσ', hK'⟩ := GlobalTheory.ConjTwist.conj_twist_isKTypeOf k _ 0 H σ hσ hK

  obtain ⟨E, iE1, iE2, iE3, π, J, hJ, hπ, hπK, hπJ⟩ := exists_conjugate_type k _ H _ hσ' hK'
  have hJσ : ∀ g u, π g (J u) = J (σ g u) := by
    intro g u
    rw [hπJ]
    simp only [zpow_zero, one_smul, map_star_star]

  have hlow : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -lamH (Fin.rev i)) =
      fun a => ((0 : ℤ) : ℝ) - Formalism.QuantumDeterminants.lowK (allPos k) lamH (Fin.rev a) := by
    rw [GlobalTheory.ConjTypeW.lowK_neg_rev]
    funext a
    simp
  have hnt : Nontrivial E := by
    obtain ⟨-, -, -, ⟨v, -, hv0, -⟩, -⟩ := hπK
    exact ⟨⟨v, 0, hv0⟩⟩
  have hHC : IsHCTypeU k (fun i => -lamH (Fin.rev i)) π := ⟨hnt, iE3, hπ, by rw [hlow]; exact hπK⟩

  obtain ⟨jE, hmem, hsurj, hfock, heq⟩ :=
    GlobalTheory.WeylConjType.exists_conj_weyl k n h lam _ hrho E π hHC

  let j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    { toFun := fun ξ => jE (J ξ)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun c x => by
        rw [map_smulₛₗ, map_smulₛₗ, RingHom.id_apply, Complex.conj_conj] }
  have hj : ∀ ξ, j ξ = jE (J ξ) := fun _ => rfl

  let Φ : H →ₗ[ℂ] ConjSp E :=
    { toFun := fun ξ => ConjSp.mk (J ξ)
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by
        show ConjSp.mk (J (c • x)) = c • ConjSp.mk (J x)
        have e := (ConjSp.mkL E).map_smulₛₗ (starRingEnd ℂ c) (J x)
        rw [Complex.conj_conj] at e
        rw [map_smulₛₗ]
        exact e }
  have hΦ : Function.Bijective Φ := hJ
  let Ψ : H ≃ₗ[ℂ] ConjSp E := LinearEquiv.ofBijective Φ hΦ
  let f := stdOrthonormalBasis ℂ (ConjSp E)
  refine ⟨j, _, f.toBasis.map Ψ.symm, fun ξ => hmem _, fun p hp => ?_, fun a a' => ?_, fun g hg ξ => ?_⟩
  · obtain ⟨η, rfl⟩ := hsurj p hp
    obtain ⟨ξ, rfl⟩ := hJ.2 η
    exact ⟨ξ, rfl⟩
  · have hb : ∀ a, J ((f.toBasis.map Ψ.symm) a) = ConjSp.out (f a) := by
      intro a
      rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
      have := Ψ.apply_symm_apply (f a)
      exact this
    rw [hj, hj, hfock, hb, hb]
    show ⟪f a', f a⟫_ℂ = _
    rw [orthonormal_iff_ite.1 f.orthonormal]
    rcases eq_or_ne a a' with rfl | hA
    · simp
    · rw [if_neg hA.symm, if_neg hA]
  · rw [hj, hj, ← hJσ, heq g hg]

end GlobalTheory.DualWeylType
