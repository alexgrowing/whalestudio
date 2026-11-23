import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalExcisionBoundaryEtaleNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExtendClassCoprimeEtaleExcisionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem mvRefine (L1 : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0) (L2 : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a) : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  intro q A A' _ _ _ f hA' n i x hx1 hx2
  obtain ⟨δ, hδex, hδref⟩ := L1 q A A' f hA' n i
  obtain ⟨w, rfl⟩ := (hδex x).1 (by simp [hx1, hx2])
  refine ⟨w, ?_⟩
  intro g hfg A₂ C _ _ _ _ _ _ hA₂ hg hC a ha hcomp
  obtain ⟨b, hb⟩ := L2 q A C f g hfg hC n i a ha
  have hf2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hg2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ g)) := hg.map _
  let φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (algebraMap A A' f)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A' A₂))
      (by simpa [← IsScalarTower.algebraMap_apply] using hf2)
  let ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (f * g)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A A₂))
      (by simpa using hf2.mul hg2)
  have hfg' : IsUnit (algebraMap A (Localization.Away (f * g)) f) :=
    isUnit_of_mul_isUnit_left (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
  let ρ : Localization.Away f →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift f (g := algebraMap A (Localization.Away (f * g))) hfg'
  have hφ : φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) := IsLocalization.Away.lift_comp _ _
  have hψ : ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) := IsLocalization.Away.lift_comp _ _
  have hρ : ρ.comp (algebraMap A _) = algebraMap A _ := IsLocalization.Away.lift_comp _ _
  have hψρ : ψ.comp ρ = Localization.awayMap (algebraMap A A₂) f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, hρ, hψ]
    exact (IsLocalization.map_comp _).symm
  refine hδref A₂ hA₂ φ hφ w b ?_
  rw [hcomp φ ψ hφ hψ, ← hb ρ hρ, ← pull_comp, ← spMap_comp_ring, hψρ]

theorem mvRefine_main : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := mvRefine GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision

end GlobalTheory.EtC
