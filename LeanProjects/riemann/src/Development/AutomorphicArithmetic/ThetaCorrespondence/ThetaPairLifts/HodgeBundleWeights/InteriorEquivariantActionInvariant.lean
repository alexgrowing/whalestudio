import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStabilizerAction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStabilizerActionStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvInterior
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}
section Moves
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)
end Moves
section Lift
variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
end Lift
section Move
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Move
section Laws
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Laws
theorem equivariant_action_preserves_interior : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  intro _ E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ
  refine ⟨fun γ => nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).hom (hρ γ),
    ⟨fun γ => nF_cart hpq hA TF Z _ _ (hρ γ), fun γ a => act_nF hpq hA TF Z _ _ (hρ γ) a, fun γ₁ γ₂ => ?_⟩,
    fun γ a b hab w w' hw hw' hb ha => ?_⟩
  · apply hom_ext' TF Z
    · rw [nF_snd, Category.assoc, nF_snd, ← Category.assoc, nF_snd, Category.assoc, map_mul, Aut.Aut_mul_def]
      rfl
    · rw [nF_toU, Category.assoc, nF_toU, ← Category.assoc, nF_toU, Category.assoc, ← nu_mul hpq hA Xo c, map_mul,
        mul_inv_rev]
  · apply hom_ext' TF Z
    · rw [Category.assoc, nF_snd, ← Category.assoc, Category.assoc (ρ γ).hom]
      erw [hw, hw']
      rw [Category.id_comp, Category.comp_id]
    · have hq : b - liftLa (ι γ)⁻¹ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq]
        exact hab.trans (liftLa_spec (ι γ)⁻¹ a).symm
      have L : (w ≫ nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).hom (hρ γ)) ≫ toU TF Z =
          i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left ≫ (nu hpq hA Xo (ι γ)⁻¹).φ := by
        rw [Category.assoc, nF_toU, ← Category.assoc, sec_toU TF Z b w hw hb, Category.assoc, Category.assoc]
      have R : ((ρ γ).hom ≫ w') ≫ toU TF Z = (ρ γ).hom ≫ i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta a).left := by
        rw [Category.assoc, sec_toU TF Z a w' hw' ha]
      rw [L, R, GlobalTheory.LevelActionLaws.eta_congr Xo hq, (nu_spec hpq hA Xo (ι γ)⁻¹).2.1 a,
        ← Category.assoc (pullback.fst _ _), ← GlobalTheory.CompLevelStab.mvF_fst]
      simp only [← Category.assoc]
      rw [← hρ γ]
end GlobalTheory.EqvInterior
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interior_equivariant_action_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  first | exact @_root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | exact _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | (intros; apply _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior <;> assumption)
end
