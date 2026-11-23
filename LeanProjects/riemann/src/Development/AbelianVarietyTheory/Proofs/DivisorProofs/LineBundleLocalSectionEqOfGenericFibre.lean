import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem genPt_dom {S : Scheme.{0}} [IsIntegral S] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    (hξ : Set.range ξ = {genericPoint S}) : QuasiCompact ξ ∧ IsSchemeTheoreticallyDominant ξ := by
  have hd : IsDominant ξ := ⟨by
    show Dense (Set.range ξ)
    rw [hξ]
    exact dense_iff_closure_eq.2 (genericPoint_spec S)⟩
  refine ⟨⟨fun U _ _ => (Set.subsingleton_of_subsingleton).isCompact⟩, ?_⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant ξ

theorem app_snd_injective {S : Scheme.{0}} [IsIntegral S] (G : Over S) [Flat G.hom] {K : Type} [Field K]
    (ξ : Sp K ⟶ S) (hξ : Set.range ξ = {genericPoint S}) (O : G.left.Opens) :
    Function.Injective ((snd (Over.mk ξ) G).left.app O).hom := by
  obtain ⟨_, _⟩ := genPt_dom ξ hξ
  have hP : IsPullback (fst (Over.mk ξ) G).left (snd (Over.mk ξ) G).left ξ G.hom := .of_hasPullback _ _
  have : IsSchemeTheoreticallyDominant (snd (Over.mk ξ) G).left := IsSchemeTheoreticallyDominant.of_isPullback hP
  have : QuasiCompact (snd (Over.mk ξ) G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP inferInstance
  exact (snd (Over.mk ξ) G).left.app_injective O

theorem locSec_eq_of_genIs : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S), Set.range ξ = {genericPoint S} →
    ∀ (N N' : S.Opens) (s : LocSec G L N) (s' : LocSec G L N') (v : SecM G L 1 (Over.mk ξ)),
      GenIs ξ s v → GenIs ξ s' v → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i) := by
  intro S _ G _ _ hG L K _ ξ hξ N N' s s' v ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ i
  have := hG.smooth
  have hfl : Flat G.hom := inferInstance
  have e := congrFun (e₁.trans e₂.symm) (fun _ => i)
  have h₃ : Set.range ξ ⊆ ((N ⊓ N' : S.Opens) : Set S) := fun x hx => ⟨h₁ hx, h₂ hx⟩
  set O : G.left.Opens := L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') with hO
  set W : (Over.mk ξ ⊗ G).left.Opens := (LPow G L 1 (Over.mk ξ)).U (fun _ => i) with hW
  have hle : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ O := lpow_U_le h₃ (fun _ => i)
  have hge : (snd (Over.mk ξ) G).left ⁻¹ᵁ O ≤ W := fun y hy => Set.mem_iInter.2 fun _ => hy.1
  have hinj : Function.Injective ((snd (Over.mk ξ) G).left.appLE O W hle).hom := by
    have hEq : W = (snd (Over.mk ξ) G).left ⁻¹ᵁ O := le_antisymm hle hge
    clear_value W
    subst hEq
    rw [← Scheme.Hom.app_eq_appLE]
    exact app_snd_injective G ξ hξ O
  apply hinj
  have k₁ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i)) = genPull h₁ s (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have k₂ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) = genPull h₂ s' (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  exact k₁.trans (e.trans k₂.symm)

end GlobalTheory.UMin.ThBdl
