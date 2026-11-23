import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

namespace GlobalTheory.TopFrameEt

theorem isFreeGen_dForm_of_formallyEtale_mvPolynomial :
    ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  intro k A₀ A _ _ _ α β ρ hc n r z b hb t hφ
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A₀ A := IsScalarTower.of_algebraMap_eq' hc.symm
  let φ := MvPolynomial.eval₂Hom ρ t
  letI : Algebra (MvPolynomial (Fin r) A₀) A := φ.toAlgebra
  haveI : IsScalarTower A₀ (MvPolynomial (Fin r) A₀) A :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = φ (MvPolynomial.C a)
      simp [φ, RingHom.algebraMap_toAlgebra]
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) A₀) A := hφ
  haveI : Algebra.FormallySmooth A₀ A :=
    Algebra.FormallySmooth.comp A₀ (MvPolynomial (Fin r) A₀) A
  haveI : Subsingleton (Algebra.H1Cotangent A₀ A) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ A) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A₀ A y).1 hy
    rw [Subsingleton.elim w 0, map_zero]
  let w : Module.Basis (Fin r) A (Ω[A⁄A₀]) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale A₀ (MvPolynomial (Fin r) A₀) A).basis
      (KaehlerDifferential.mvPolynomialBasis A₀ (Fin r))
  have hw : ∀ i, w i = KaehlerDifferential.D A₀ A (t i) := fun i ↦ by
    simp [w, IsBaseChange.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.map_D, RingHom.algebraMap_toAlgebra, φ]
  obtain ⟨B, hB⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k A₀ A) (KaehlerDifferential.map k A₀ A A) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k A₀ A)
    (b.baseChange A) w (fun i ↦ KaehlerDifferential.D k A (t i))
    (fun i ↦ by rw [hw, KaehlerDifferential.map_D]; rfl)
  let e : Fin (r + n) ≃ Fin n ⊕ Fin r := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  refine isFreeGen_dForm _ (B.reindex e.symm) fun a ↦ ?_
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) a
  · simp [e, Fin.append_left]
  · simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply,
      Sum.swap_inr, Sum.elim_inl, Module.Basis.baseChange_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, hb, dFun, KaehlerDifferential.map_D,
      Fin.append_right]
    rfl

end GlobalTheory.TopFrameEt
