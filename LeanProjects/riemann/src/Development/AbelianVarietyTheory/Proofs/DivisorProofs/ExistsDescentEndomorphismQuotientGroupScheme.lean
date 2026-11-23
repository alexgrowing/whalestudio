import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem epi_of_isPullback_galois {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (hc : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {a : P ⟶ X} {b : P ⟶ Q} {c : Q ⟶ Y} (h : IsPullback a b π c) : Epi b := by
  have e := h.flip.isoPullback_hom_fst
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst hc c
  rw [← e]
  exact epi_comp _ _

variable {S : Scheme.{0}}

theorem isPullback_whiskerRight_fst {A A' : Over S} (ψ : A ⟶ A') (B : Over S) :
    IsPullback (pullback.fst A.hom B.hom) (ψ ▷ B).left ψ.left (pullback.fst A'.hom B.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd A'.hom B.hom) (v₂₂ := A'.hom) (h₃₁ := B.hom) ?_
    (Over.whiskerRight_left_fst ψ).symm (IsPullback.of_hasPullback A'.hom B.hom)
  rw [Over.whiskerRight_left_snd, Over.w]
  exact IsPullback.of_hasPullback A.hom B.hom

theorem isPullback_whiskerLeft_snd {A A' : Over S} (ψ : A ⟶ A') (B : Over S) :
    IsPullback (pullback.snd B.hom A.hom) (B ◁ ψ).left ψ.left (pullback.snd B.hom A'.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.fst B.hom A'.hom) (v₂₂ := A'.hom) (h₃₁ := B.hom) ?_
    (Over.whiskerLeft_left_snd ψ).symm (IsPullback.of_hasPullback B.hom A'.hom).flip
  rw [Over.whiskerLeft_left_fst, Over.w]
  exact (IsPullback.of_hasPullback B.hom A.hom).flip

theorem exists_desc_endo (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A') (hψ : IsMonHom ψ)
    (hc : GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left)
    (f : A ⟶ A) (hf : IsMonHom f) (hH : ∀ h ∈ H, h ≫ f ∈ H) :
    ∃ f' : A' ⟶ A', IsMonHom f' ∧ ψ ≫ f' = f ≫ ψ := by

  have kill : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hc.inv ⟨h, hh⟩)
  have inv : ∀ a : H, (transl a.1).left ≫ f.left ≫ ψ.left = f.left ≫ ψ.left := by
    intro a
    have e : transl a.1 ≫ f ≫ ψ = f ≫ ψ := by
      have k1 : toUnit A ≫ a.1 ≫ f ≫ ψ = 1 := by
        rw [← Category.assoc a.1, kill _ (hH _ a.2), comp_one]
      rw [transl, MonObj.mul_comp, Category.id_comp, Category.assoc, k1, _root_.mul_one]
    simpa using congrArg Over.Hom.left e
  obtain ⟨g, hg, -⟩ := hc.existsUnique_desc (f.left ≫ ψ.left) inv
  have hepi := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hc
  have gw : g ≫ A'.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ A' := Over.homMk g gw
  have hf' : ψ ≫ f' = f ≫ ψ := Over.OverMorphism.ext (by simpa [f'] using hg)
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', ← Category.assoc, IsMonHom.one_hom f]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback_galois hc (isPullback_whiskerRight_fst ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback_galois hc (isPullback_whiskerLeft_snd ψ A')
    have : Epi (ψ ⊗ₘ ψ) := by
      rw [MonoidalCategory.tensorHom_def]
      have := Over.epi_of_epi_left (ψ ▷ A)
      have := Over.epi_of_epi_left (A' ◁ ψ)
      exact epi_comp _ _
    rw [← cancel_epi (ψ ⊗ₘ ψ), ← reassoc_of% (IsMonHom.mul_hom ψ), hf', ← Category.assoc,
      IsMonHom.mul_hom f, Category.assoc, IsMonHom.mul_hom ψ]
    simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hf']

end GlobalTheory.UPel.HT.Hecke
