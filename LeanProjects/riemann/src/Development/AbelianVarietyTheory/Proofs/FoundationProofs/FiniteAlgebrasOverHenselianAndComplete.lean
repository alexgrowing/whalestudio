import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

noncomputable section

namespace GlobalTheory

open IsLocalRing TensorProduct

universe u

open IsLocalRing TensorProduct in
open WithConv in

theorem _root_.GlobalTheory.bialgHom_map_antipode {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (g : A →ₐc[R] B) (a : A) :
    g (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (g a) := by
  have h1 := LinearMap.algHom_comp_convMul_distrib (g : A →ₐ[R] B)
    (toConv (HopfAlgebra.antipode R)) (toConv LinearMap.id)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib (toConv LinearMap.id)
    (toConv (HopfAlgebra.antipode R)) (g : A →ₗc[R] B)
  have e1 : (g : A →ₐ[R] B).toLinearMap ∘ₗ ofConv (1 : WithConv (A →ₗ[R] A)) =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp only [LinearMap.convOne_def]
    exact (g : A →ₐ[R] B).commutes _
  have e2 : ofConv (1 : WithConv (B →ₗ[R] B)) ∘ₗ (g : A →ₗc[R] B).toLinearMap =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp [LinearMap.convOne_def]
  rw [LinearMap.antipode_mul_id, e1] at h1
  rw [LinearMap.id_mul_antipode, e2] at h2
  have h := left_inv_eq_right_inv (ofConv_injective h1).symm (ofConv_injective h2).symm
  simpa using congrArg (fun f : WithConv (A →ₗ[R] B) ↦ (ofConv f) a) h

open IsLocalRing TensorProduct in

theorem _root_.GlobalTheory.henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  _root_.GlobalTheory.henselianLocalRing_of_henselianRing R

open IsLocalRing TensorProduct in

theorem _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable (R : Type u) (L : Type*) [CommRing R]
    [HenselianLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [Module.Finite (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  obtain ⟨A, _, _, hfin, het, hloc, he⟩ := _root_.GlobalTheory.exists_etale_lift_of_isSeparable R L
  exact ⟨A, inferInstance, inferInstance, hfin, het, _root_.GlobalTheory.henselianLocalRing_of_finite R A, he⟩

open IsLocalRing TensorProduct in
open CategoryTheory in

theorem _root_.GlobalTheory.finite_algebras_over_henselian (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      (∃ (ι : Type u) (_ : Finite ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
        (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
        ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i)) ∧
      ∀ c : S ⧸ (maximalIdeal R).map (algebraMap R S), IsIdempotentElem c →
        ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c) ∧
    (CommAlgCat.FiniteEtale.baseChange.{u} R (ResidueField R)).IsEquivalence ∧
    ∀ (L : Type u) [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
      [Algebra.IsSeparable (ResidueField R) L],
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
        HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  refine ⟨fun S _ _ _ ↦ ⟨_root_.GlobalTheory.exists_algEquiv_pi_henselianLocalRing R S,
    fun c hc ↦ _root_.GlobalTheory.existsUnique_idempotent_lift_quotient R hc⟩, ?_,
    fun L _ _ _ _ ↦ _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable R L⟩
  refine
    { faithful := ⟨fun {X Y} f g h ↦ ?_⟩
      full := ⟨fun {X Y} φ ↦ ?_⟩
      essSurj := ⟨fun Y ↦ ?_⟩ }
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    exact ObjectProperty.hom_ext _ (CommAlgCat.hom_ext
      ((_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).1
        (congrArg (fun φ ↦ φ.hom.hom) h)))
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    obtain ⟨f, hf⟩ := (_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).2 φ.hom.hom
    exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom f),
      ObjectProperty.hom_ext _ (CommAlgCat.hom_ext hf)⟩
  · have : Algebra.Etale (ResidueField R) Y.obj := Y.property.2
    obtain ⟨A, _, _, hfin, het, ⟨e⟩⟩ := _root_.GlobalTheory.exists_etale_lift_of_etale.{u, u} R Y.obj
    exact ⟨⟨CommAlgCat.of R A, ⟨hfin, het⟩⟩, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

end GlobalTheory
