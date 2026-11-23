import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDualsStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem isDefGram_map {E K : Type} [Field E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) (f : E →+* K)
    (hf : ∀ x, star (f x) = f (cE x)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ φ : E →+* ℂ, (A.map φ).PosDef) : IsDefGram (A.map f) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun (hA (σ.comp f)).isHermitian.eq a) b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h ⊢
    rw [hf]
    apply σ.injective
    have h2 := hc (σ.comp f) (A b a)
    simp only [RingHom.comp_apply] at h h2
    rw [h2]
    exact h
  · intro a b ψ
    simp only [Matrix.map_apply]
    rw [hf]
    exact hc (ψ.comp f) _
  · intro φ
    rw [Matrix.map_map]
    exact hA (φ.comp f)

theorem map_inv_of_isUnit_det {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hA : IsUnit A.det) : (A.map f)⁻¹ = A⁻¹.map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA]
  simp

theorem isUnit_det_map {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) : IsUnit (A.map f).det ↔ IsUnit A.det := by
  have : (A.map f).det = f A.det := by rw [RingHom.map_det]; rfl
  rw [this, isUnit_iff_ne_zero, isUnit_iff_ne_zero, map_ne_zero]

theorem defGram_selfDual_of_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  intro E K _ _ _ _ _ cE hc ι emb hemb n J hJ τ
  obtain ⟨φ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hdet : IsUnit J.det :=
    (isUnit_det_map φ₀ J).1 ((Matrix.isUnit_iff_isUnit_det _).1 (hJ φ₀).isUnit)
  have h1 : IsDefGram (gramK emb J τ) := isDefGram_map cE hc (emb τ) (hemb τ) J hJ
  have hdK : IsUnit (gramK emb J τ).det := (isUnit_det_map (emb τ) J).2 hdet
  refine ⟨h1, ?_, ?_⟩
  · have e : gramKd emb J τ = ((J⁻¹)ᵀ).map (emb τ) := by
      unfold gramKd
      rw [map_inv_of_isUnit_det _ _ hdet, Matrix.transpose_map]
    rw [e]
    refine isDefGram_map cE hc (emb τ) (hemb τ) _ fun φ => ?_
    rw [Matrix.transpose_map, ← map_inv_of_isUnit_det _ _ hdet]
    exact (hJ φ).inv.transpose
  · intro L hL
    have hl : Submodule.IsLattice K (tauLat emb τ L) := GlobalTheory.T.lattice_extension_along_field_embedding_duals.1 E K ι n emb τ L hL.1
    have hd : hdualFr (gramK emb J τ) (tauLat emb τ L) = tauLat emb τ L :=
      GlobalTheory.T.lattice_extension_along_field_embedding_duals.2.1 E K ι n emb cE τ (hemb τ) J L L hdet hL.1 hL.2
    refine ⟨⟨hl, hd⟩, (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K n _ _ hdK hl).1, ?_⟩
    have h := GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.2 K n _ _ h1.1 hdK hl
    rw [hd] at h
    exact h

end GlobalTheory.TestLat
