import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelDirect

open GlobalTheory.SiegelPullComp

private theorem tensor_left_hom_ext' {T : Scheme.{0}} {G : Over T} {X : Scheme.{0}} (a b : X ⟶ (G ⊗ G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key := CartesianMonoidalCategory.hom_ext
    (Over.homMk a rfl : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) (Over.homMk b hw)
    (by ext; simpa using h1) (by ext; simpa using h2)
  simpa using congrArg (fun k => k.left) key

theorem exists_inverse {T : Scheme.{0}} {A G : Over T} [GrpObj A] [GrpObj G] {φ : A.left ⟶ G.left}
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hφ : IsGrpPullback A G (𝟙 T) φ) (hs : Geo.Tor.IsSquare φ φ₂) :
    ∃ (F : G.left ⟶ A.left) (F₂ : (G2 G).left ⟶ (G2 A).left), IsGrpPullback G A (𝟙 T) F ∧ Geo.Tor.IsSquare F F₂ ∧
      φ ≫ F = 𝟙 _ ∧ F₂ ≫ φ₂ = 𝟙 _ := by
  have hw : φ ≫ G.hom = A.hom := by simpa using hφ.1.w
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  let e : A ≅ G := Over.isoMk (asIso φ) hw
  have heL : e.inv.left = inv φ := rfl
  have hsF : Geo.Tor.IsSquare (inv φ) (e.inv ⊗ₘ e.inv).left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst, Over.comp_left, heL]
    · rw [← Over.comp_left, tensorHom_snd, Over.comp_left, heL]
  refine ⟨inv φ, (e.inv ⊗ₘ e.inv).left, ⟨?_, ?_⟩, hsF, by simp, ?_⟩
  · refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← hw]
    simp
  · intro U x y x₀ y₀ hx hy
    have key := hφ.2 (Over.mk (U.hom ≫ 𝟙 T)) x₀ y₀ (Over.homMk x.left (by simp))
      (Over.homMk y.left (by simp)) (by simp [hx]) (by simp [hy])
    have hxy := mul_left_congr (a := (U.hom ≫ 𝟙 T) ≫ 𝟙 T) (b := U.hom) (by simp)
      (Over.homMk x.left (by simp)) (Over.homMk y.left (by simp)) x y (by simp) (by simp)
    rw [hxy.symm.trans key]
    simp
  · apply tensor_left_hom_ext'
    · rw [Category.assoc, hs.1, ← Category.assoc, hsF.1]
      simp
    · rw [Category.assoc, hs.2, ← Category.assoc, hsF.2]
      simp

theorem direct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), SiegData sT t lev Ag z bas w → ∃ (θ : t.G.left ⟶ Ag.univ.A.left) (θ₂ : (G2 t.G).left ⟶ (G2 Ag.univ.A).left), IsGrpPullback t.G Ag.univ.A (w ≫ pullback.fst _ _) θ ∧ IsSquare θ θ₂ ∧ LBIso (abelian₂ t.G t.PP.L) (Ag.univ.P.pull θ₂) ∧ ∀ u, (lev (bas u)).left ≫ θ = (w ≫ pullback.fst _ _) ≫ (Ag.univ.lev u).left := by
  intro E _ _ _ H D O _ T sT t lev g p N Ag z bas w hd
  obtain ⟨o, φ, φ₂, hφ, hs, hL, hlev, hcl, ψ, ψ₂, hψ, hs', hP, hlev'⟩ := hd
  obtain ⟨F, F₂, hF, hsF, hφF, hF₂⟩ := exists_inverse hφ hs
  have h0 : t.PP.L.IsLB := t.PP.isLB
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := by
    unfold abelian₂
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ h0 _ _
  refine ⟨F ≫ ψ, F₂ ≫ ψ₂, (hF.comp hψ).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hs'.1, ← Category.assoc, hsF.1, Category.assoc]
  · rw [Category.assoc, hs'.2, ← Category.assoc, hsF.2, Category.assoc]
  · have hΛ₁ := pull_isLB hΛ (𝟙 (G2 t.G).left)
    have hΛ₂ := pull_isLB (pull_isLB hΛ φ₂) F₂
    have hO := pull_isLB o.isLB F₂
    have hU₁ := pull_isLB (pull_isLB Ag.univ.isLB ψ₂) F₂
    have hU₂ := pull_isLB Ag.univ.isLB (F₂ ≫ ψ₂)
    have s1 : LBIso (abelian₂ t.G t.PP.L) ((abelian₂ t.G t.PP.L).pull (𝟙 _)) := iso_pull_id hΛ
    have s2 : LBIso ((abelian₂ t.G t.PP.L).pull (𝟙 _)) (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) := by
      have k := iso_pull_pull hΛ φ₂ F₂
      rw [hF₂] at k
      exact k.symm
    have s3 : LBIso (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) (o.P.pull F₂) := (iso_pull F₂ hL).symm
    have s4 : LBIso (o.P.pull F₂) ((Ag.univ.P.pull ψ₂).pull F₂) := iso_pull F₂ hP
    have s5 : LBIso ((Ag.univ.P.pull ψ₂).pull F₂) (Ag.univ.P.pull (F₂ ≫ ψ₂)) := iso_pull_pull Ag.univ.isLB ψ₂ F₂
    exact LBIso.trans hΛ hΛ₁ hU₂ s1 (LBIso.trans hΛ₁ hΛ₂ hU₂ s2
      (LBIso.trans hΛ₂ hO hU₂ s3 (LBIso.trans hO hU₁ hU₂ s4 s5)))
  · intro u
    rw [← hlev u]
    simp only [Category.assoc, reassoc_of% hφF]
    exact hlev' u

end GlobalTheory.SiegelDirect

end
