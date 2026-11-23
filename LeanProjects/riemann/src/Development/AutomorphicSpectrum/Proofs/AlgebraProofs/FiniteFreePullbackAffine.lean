import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

theorem finiteFreeHom_algebraMap_iff {A B : Type} [CommRing A] [CommRing B] [Algebra A B] :
    FiniteFreeHom (algebraMap A B) ↔ Module.Free A B ∧ Module.Finite A B := by
  have h : (algebraMap A B).toAlgebra = ‹Algebra A B› := Algebra.algebra_ext _ _ fun _ => rfl
  simp only [GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom]
  rw [h]

theorem finiteFreeHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : FiniteFreeHom f) (hg : FiniteFreeHom g) :
    FiniteFreeHom (g.comp f) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hf₁, hf₂⟩ := hf
  obtain ⟨hg₁, hg₂⟩ := hg
  exact ⟨Module.Free.trans (S := B), Module.Finite.trans B C⟩

theorem finiteFreeHom_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    FiniteFreeHom e.toRingHom := by
  letI := e.toRingHom.toAlgebra
  let l : A ≃ₗ[A] B := { e with map_smul' := fun a x => map_mul e a x }
  exact ⟨Module.Free.of_equiv l, Module.Finite.equiv l⟩

theorem finiteFreeHom_stableUnderComposition :
    RingHom.StableUnderComposition (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  intro A B C _ _ _ f g hf hg
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_comp f g hf hg

theorem finiteFreeHom_respectsIso :
    RingHom.RespectsIso (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) :=
  RingHom.StableUnderComposition.respectsIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_stableUnderComposition
    fun e => GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_ringEquiv e

theorem finiteFreeHom_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  refine RingHom.IsStableUnderBaseChange.mk GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso ?_
  intro R S T _ _ _ _ _ h
  obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.1 h
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.2 ⟨inferInstance, inferInstance⟩

theorem finiteFreeHom_appTop_of_isPullback :
    ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by
  intro P Q D W u v g h _ _ _ _ hpb hg
  have hbc := RingHom.IsStableUnderBaseChange.pullback_fst_appTop @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom
    GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_isStableUnderBaseChange GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso h g hg
  haveI : IsIso hpb.flip.isoPullback.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso hpb.flip.isoPullback.op).isIso_hom
  rw [← hpb.flip.isoPullback_hom_fst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  exact (RingHom.RespectsIso.cancel_right_isIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso _ _).2 hbc

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
