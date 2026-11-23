import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam
open GlobalTheory.ZM.SiegPull

theorem LamIs.comp {S S' S'' : Scheme.{0}} {A' : Over S''} [GrpObj A'] {A : Over S'} [GrpObj A] {B : Over S}
    {L' : LB A'.left} {L : LB A.left} {Pb : LB (B ⊗ B).left} {ψ : A'.left ⟶ A.left} {φ : A.left ⟶ B.left}
    (hL' : L'.IsLB) (hL : L.IsLB) (hP : Pb.IsLB) (h' : LamIs A' L' A (abelian₂ A L) ψ) (h : LamIs A L B Pb φ) :
    LamIs A' L' B Pb (ψ ≫ φ) := by
  obtain ⟨ψ₂, sψ, iψ⟩ := h'
  obtain ⟨φ₂, sφ, iφ⟩ := h
  exact ⟨ψ₂ ≫ φ₂, isSquare_comp sψ sφ, LBIso.trans (DVR.linComb_isLB _ hL' _ _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (pull_isLB hP _) iψ (lbIso_pull_comp iφ ψ₂)⟩

theorem PolPB.lamIs {S S' : Scheme.{0}} {P' : Out.PolAV S'} {P : Out.PolAV S} {f : S' ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} (h : PolPB P' P f φ) : LamIs P'.A P'.L P.A (abelian₂ P.A P.L) φ := by
  letI := P.isAb.comm
  letI := P'.isAb.comm
  obtain ⟨φ₂, s⟩ := exists_isSquare h.1.1.w
  exact ⟨φ₂, s, lbIso_lam_pull h.1 h.2.2 s⟩

theorem sqOf_calculus : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : S' ⟶ S), (∀ (g : S'' ⟶ S') (P : Out.PolAV S') (P' : Out.PolAV S'') (φ : P.A.left ⟶ c.A.left) (ψ : P'.A.left ⟶ P.A.left), SqOf P c f φ → PolPB P' P g ψ → SqOf P' c (g ≫ f) (ψ ≫ φ)) ∧ (∀ (P P' : Out.PolAV S') (φ : P.A.left ⟶ c.A.left) (φ' : P'.A.left ⟶ c.A.left), SqOf P c f φ → SqOf P' c f φ' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ e.hom.left ≫ φ = φ' ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left) ∧ ∀ (P P' : Out.PolAV S') (φ : P.A.left ⟶ c.A.left) (e : P'.A ≅ P.A), IsMonHom e.hom → P'.g = P.g → LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left → SqOf P c f φ → SqOf P' c f (e.hom.left ≫ φ) := by
  intro h k o _ ζ S S' S'' s c f
  refine ⟨fun g P P' φ ψ H H' => ⟨H'.1.comp H.1, H'.2.1.trans H.2.1,
      LamIs.comp P'.isLB P.isLB c.isLB H'.lamIs H.2.2⟩, fun P P' φ φ' H H' => ?_,
    fun P P' φ e he hg hl H => ⟨((isGrpPullback_of_iso e).comp H.1).congr (Category.id_comp _) rfl,
      hg.trans H.2.1, LamIs.comp P'.isLB P.isLB c.isLB hl H.2.2⟩⟩
  obtain ⟨e, he, hφ⟩ := grpPullback_iso H'.1 H.1
  obtain ⟨φ₂, s₂, i₂⟩ := H.2.2
  obtain ⟨φ₂', s₂', i₂'⟩ := H'.2.2
  refine ⟨e, he, hφ, _, isSquare_tensor e.hom, ?_⟩
  have k₁ := lbIso_pull_comp i₂ (e.hom ⊗ₘ e.hom).left
  rw [isSquare_unique (isSquare_comp (isSquare_tensor e.hom) s₂) s₂' hφ] at k₁
  exact LBIso.trans (DVR.linComb_isLB _ P'.isLB _ _) (pull_isLB c.isLB _)
    (pull_isLB (DVR.linComb_isLB _ P.isLB _ _) _) i₂' k₁.symm

end GlobalTheory.KeyFam
