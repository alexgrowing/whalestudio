import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalIsometryEqualRank

theorem exists_of_frames {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (hr : m = n)
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A) (h : GL (Fin n) A) (h' : GL (Fin m) A)
    (h2 : (h.1.map σ)ᵀ * J * h.1 = 1) (h2' : (h'.1.map σ)ᵀ * J' * h'.1 = 1) (S : Subring A) :
    ∃ (φ : Matrix (Fin m) (Fin n) A) (ψ : Matrix (Fin n) (Fin m) A), φ * ψ = 1 ∧ ψ * φ = 1 ∧
      ((φ.map σ)ᵀ * J' : Matrix (Fin n) (Fin m) A) * φ = J ∧
      ∀ x, (∀ i, (h⁻¹).1.mulVec x i ∈ S) ↔ (∀ i, (h'⁻¹).1.mulVec (φ.mulVec x) i ∈ S) := by
  subst hr
  refine ⟨(h' * h⁻¹).1, (h * h'⁻¹).1, ?_, ?_, ?_, fun x => ?_⟩
  · rw [← Units.val_mul]; simp
  · rw [← Units.val_mul]; simp
  · have e : ((h⁻¹).1.map σ)ᵀ * (h.1.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
    have e2 : h.1 * (h⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((h⁻¹).1.map σ)ᵀ * (h'.1.map σ)ᵀ * J' * (h'.1 * (h⁻¹).1)
        = ((h⁻¹).1.map σ)ᵀ * ((h'.1.map σ)ᵀ * J' * h'.1) * (h⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = ((h⁻¹).1.map σ)ᵀ * ((h.1.map σ)ᵀ * J * h.1) * (h⁻¹).1 := by rw [h2, h2']
      _ = (((h⁻¹).1.map σ)ᵀ * (h.1.map σ)ᵀ) * J * (h.1 * (h⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [e, e2, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section CM
attribute [local instance] IsCMField.starRing

theorem exists_of_cm {E : Type} [Field E] [NumberField E] [IsCMField E] (hc : CMData (maximalRealSubfield E) E)
    (V V' : HSpace E) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E))
      (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)),
      φ * ψ = 1 ∧ ψ * φ = 1 ∧
      (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) φ * JR (Fv (maximalRealSubfield E) v) V'.gram :
        Matrix (Fin V.rank) (Fin V'.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * φ =
        JR (Fv (maximalRealSubfield E) v) V.gram ∧
      ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
        φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V' v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal hc V v
  obtain ⟨h', h1', h2'⟩ := exists_orthonormal hc V' v
  obtain ⟨φ, ψ, a, b, c, d⟩ := exists_of_frames (sigR (Fv (maximalRealSubfield E) v) hc.sig) hr
    (JR (Fv (maximalRealSubfield E) v) V.gram) (JR (Fv (maximalRealSubfield E) v) V'.gram) h h' h2 h2' (ordAt E v)
  exact ⟨φ, ψ, a, b, c, fun x => (h1 x).trans ((d x).trans (h1' _).symm)⟩

end CM

theorem exists_local_isometry : ∀ (D : D7) (V V' : Formalism.BasicNotions.TH.HSp D), V'.rank = V.rank → ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)), φ * ψ = 1 ∧ ψ * φ = 1 ∧ (Formalism.UG.cT (sigR (Fv D.host.F v) D.sp.cm.sig) φ * JR (Fv D.host.F v) V'.gram : Matrix (Fin V.rank) (Fin V'.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)) * φ = JR (Fv D.host.F v) V.gram ∧ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V' v := by
  intro D V V' hr v
  have := D.host.isCMField_hostE
  have key := exists_of_cm (E := D.host.E) D.sp.cm V V' hr v
  exact key

end GlobalTheory.LocalIsometryEqualRank
