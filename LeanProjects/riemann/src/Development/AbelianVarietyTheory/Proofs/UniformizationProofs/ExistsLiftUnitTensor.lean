import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

theorem exists_lift_unit_tensor {S Z : Scheme.{0}} (X : Over S) (q : Z ⟶ X.left) :
    ∃ r : Z ⟶ (𝟙_ (Over S) ⊗ X).left, r ≫ (snd _ X).left = q ∧ r ≫ (fst _ X).left = q ≫ X.hom := by
  refine ⟨q ≫ (λ_ X).inv.left, ?_, ?_⟩
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_snd, Over.id_left, Category.comp_id]
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_fst]
    rfl

theorem expandsAt_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → U.ExpT (𝟙_ _) k σ' f' → ∀ e, U'.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  dsimp only at hL hgt hw
  subst hL hgt
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hσ
  obtain ⟨S, hS⟩ := hE e
  refine DVR.expandsAt_of_val U' e k σ f S fun y J hJ => ?_
  obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (fstG I e G).left
  obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (U'.gt e).pG.left
  have hc : (U'.gt e).pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U'.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := hS _ (𝟙 _) rG rB (hG₁.trans (Category.id_comp _).symm) (hB₁.trans (Category.id_comp _).symm)
    (hB₂.trans (hc.trans hG₂.symm)) y
  have hf : ∀ α, sval (f' α) rB y J = sval (f α) (DVR.pGl U' e) y J := fun α => by
    rw [hB α _ rB y J hJ, hB₁]
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · choose JG hJG using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U'.LG.isLB (ψ y)
    exact (hf α).symm.trans ((H JG J hJG hJ).1 α hα)
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U'.LG.L U'.LG.isLB y (fun _ : PUnit => (fstG I e G).left) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    have e₀ : JG (fstG I e G).left = jL := eJ PUnit.unit
    have H₂ := (H JG J hJG hJ).2
    have hs : sval σ' rG y JG = DVR.sv U' k σ (DVR.fGl I G e) y jL := by
      rw [hG _ rG y JG hJG, hG₁]
      exact sval_of σ _ y JG (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact e₀)
    simp only [Category.id_comp, e₀, hs, hf] at H₂
    rw [Units.val_pow_eq_pow_val]
    exact H₂

end GlobalTheory.UU
end
