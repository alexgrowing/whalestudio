import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EighthPowerUnits

section Rel

variable {S' S : Scheme.{0}} {j : S' ⟶ S} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (hφ : IsGrpPullback G' G j φ) :
    (1 : G' ⟶ G').left ≫ φ = φ ≫ (1 : G ⟶ G).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  let z : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
    (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl)
  have h := hφ.2 G' 1 1 z z rfl rfl
  rw [_root_.mul_one] at h
  have hz : z = 1 := mul_eq_left.1 (Over.OverMorphism.ext h)
  have h1 : φ₀ ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have h2 : z.left = (φ₀ ≫ (1 : G ⟶ G)).left := congrArg (fun w => w.left) (hz.trans h1.symm)
  rw [Over.comp_left] at h2
  exact h2

theorem mul_left_comp (hφ : IsGrpPullback G' G j φ) {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ * e₂).left ≫ φ = φ ≫ (F₁ * F₂).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  have h := hφ.2 G' e₁ e₂ (φ₀ ≫ F₁) (φ₀ ≫ F₂) h₁.symm h₂.symm
  rw [← MonObj.comp_mul] at h
  exact h.symm

theorem comp_left_comp {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ ≫ e₂).left ≫ φ = φ ≫ (F₁ ≫ F₂).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

end Rel

theorem exists_matrixUnits_extend : ∀ {S B : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U₀ : S.Opens) (hU : Dense (U₀ : Set S)) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (G' : Over U₀.toScheme) [GrpObj G'] (P : Over B) [GrpObj P] [IsCommMonObj P] (f : U₀.toScheme ⟶ B) (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G U₀.ι φ) (hψ : IsGrpPullback G' P f ψ) (E' : Fin 8 → Fin 8 → (P ⟶ P)) (hE' : ∀ a b, IsMonHom (E' a b)) (hrel : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1) (hsum : ∏ a, E' a a = 𝟙 P), ∃ E : Fin 8 → Fin 8 → (G ⟶ G), (∀ a b, IsMonHom (E a b)) ∧ (∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) ∧ ∏ a, E a a = 𝟙 G ∧ ∀ a b, ∃ e : G' ⟶ G', IsMonHom e ∧ e.left ≫ φ = φ ≫ (E a b).left ∧ e.left ≫ ψ = ψ ≫ (E' a b).left := by
  intro S B _ hS U₀ hU G _ _ hG G' _ P _ _ f φ ψ hφ hψ E' hE' hrel hsum
  have : IsDominant U₀.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS U₀.ι
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  let e : Fin 8 → Fin 8 → (G' ⟶ G') := fun a b =>
    Over.homMk (hψ.1.lift (ψ ≫ (E' a b).left) G'.hom (by rw [Category.assoc, Over.w, hψ.1.w]))
      (hψ.1.lift_snd _ _ _)
  have he : ∀ a b, (e a b).left ≫ ψ = ψ ≫ (E' a b).left := fun a b => hψ.1.lift_fst _ _ _
  have heM : ∀ a b, IsMonHom (e a b) := fun a b => by
    haveI := hE' a b
    exact ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback hψ hψ (E' a b) (e a b) (he a b)
  have uq : ∀ {x y : G' ⟶ G'} {F : P ⟶ P}, x.left ≫ ψ = ψ ≫ F.left → y.left ≫ ψ = ψ ≫ F.left → x = y :=
    fun hx hy => Over.OverMorphism.ext (hψ.1.hom_ext (hx.trans hy.symm) ((Over.w _).trans (Over.w _).symm))
  have uG : ∀ {F₁ F₂ : G ⟶ G}, φ ≫ F₁.left = φ ≫ F₂.left → F₁ = F₂ :=
    fun h => GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 h
  have ext : ∀ a b, ∃ F : G ⟶ G, IsMonHom F ∧ (e a b).left ≫ φ = φ ≫ F.left := fun a b => by
    haveI := heM a b
    exact (GlobalTheory.Published.SemiAbelianHomExtension.of_isGrpPullback GlobalTheory.semiAbelianHomExtension_holds hS hG hG hφ hφ
      (e a b)).exists
  choose E hE using ext
  refine ⟨E, fun a b => (hE a b).1, ?_, ?_, fun a b => ⟨e a b, heM a b, (hE a b).2, he a b⟩⟩
  · intro a b c d
    apply uG
    by_cases hbc : b = c
    · subst hbc
      rw [if_pos rfl]
      have h1 := comp_left_comp (he a b) (he b d)
      rw [hrel, if_pos rfl] at h1
      have h2 : e a b ≫ e b d = e a d := uq h1 (he a d)
      rw [← comp_left_comp (hE a b).2 (hE b d).2, h2, (hE a d).2]
    · rw [if_neg hbc]
      have h1 := comp_left_comp (he a b) (he c d)
      rw [hrel, if_neg hbc] at h1
      have h2 : e a b ≫ e c d = 1 := uq h1 (one_left_comp hψ)
      rw [← comp_left_comp (hE a b).2 (hE c d).2, h2, one_left_comp hφ]
  · have key : ∀ s : Finset (Fin 8), ∃ x : G' ⟶ G', x.left ≫ φ = φ ≫ (∏ a ∈ s, E a a).left ∧
        x.left ≫ ψ = ψ ≫ (∏ a ∈ s, E' a a).left := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · refine ⟨1, ?_, ?_⟩
        · rw [Finset.prod_empty]; exact one_left_comp hφ
        · rw [Finset.prod_empty]; exact one_left_comp hψ
      · intro a s ha ih
        obtain ⟨x, h1, h2⟩ := ih
        refine ⟨e a a * x, ?_, ?_⟩
        · rw [Finset.prod_insert ha]; exact mul_left_comp hφ (hE a a).2 h1
        · rw [Finset.prod_insert ha]; exact mul_left_comp hψ (he a a) h2
    obtain ⟨x, h1, h2⟩ := key Finset.univ
    rw [hsum] at h2
    have hx : x = 𝟙 G' := uq h2 (by simp)
    apply uG
    rw [← h1, hx]
    simp

end GlobalTheory.EighthPowerUnits
