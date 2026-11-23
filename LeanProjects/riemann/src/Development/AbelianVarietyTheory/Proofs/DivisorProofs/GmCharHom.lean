import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifWeight

open ReciprocityTheory.ChartRestriction.G.DVR

section Char

variable {S : Scheme.{0}} {X X₁ X₂ : Type} [AddCommGroup X] [AddCommGroup X₁] [AddCommGroup X₂]

theorem gm_char_hom {j : X₁ → X} {τ : splitTorus S X ⟶ splitTorus S X₁} (hτ : TorusHomOf j τ) {T : Over S}
    (r : T ⟶ splitTorus S X) (y : T.left) (x : X₁) :
    gm (r ≫ τ).left y ⊤ (charUnit S X₁ x) = gm r.left y ⊤ (charUnit S X (j x)) := by
  rw [← hτ x]
  exact ((gm_res r.left y (V := ⊤) _ trivial _).trans (gm_pull r.left τ.left y ⊤ trivial _)).symm

theorem gm_char_add {T : Over S} (r : T ⟶ splitTorus S X) (y : T.left) (a b : X) :
    gm r.left y ⊤ (charUnit S X (a + b)) = gm r.left y ⊤ (charUnit S X a) * gm r.left y ⊤ (charUnit S X b) := by
  rw [PowTorusCoord.gm_char, PowTorusCoord.gm_char, PowTorusCoord.gm_char, ofAdd_add, map_mul, map_mul]

end Char

theorem val_weight {R : Type} [CommRing R] [IsDomain R] {D₁ : DegPre R} {S : Scheme.{0}} {s : S ⟶ Sp R}
    {X : Type} [AddCommGroup X] {G G₁ : Over S} [GrpObj G] [GrpObj G₁] (σ : G ⟶ G₁) [IsMonHom σ]
    {P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A} {x : D₁.X} (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ x) Oinvε))
    (κ : splitTorus S X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (τ : splitTorus S X ⟶ splitTorus S D₁.X)
    (hκ : κ ≫ σ = τ ≫ κ₁)
    (hw : LB.Gen.Corr D₁.P.L _ _ _ _
      (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left)
      (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L x)
        (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)))
    (y : (splitTorus S X ⊗ G).left) {J} (hJ : Good D₁.P.L y J) :
    val (Y := G₁.left) t₁ ((lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ).left y J =
      gm (fst (splitTorus S X) G ≫ τ).left y ⊤ (charUnit _ D₁.X x) *
        val (Y := G₁.left) t₁ (snd (splitTorus S X) G ≫ σ).left y J := by
  let N : splitTorus S X ⊗ G ⟶ splitTorus S D₁.X ⊗ G₁ := τ ⊗ₘ σ
  have n₁ : N ≫ fst _ _ = fst _ _ ≫ τ := tensorHom_fst _ _
  have n₂ : N ≫ snd _ _ = snd _ _ ≫ σ := tensorHom_snd _ _
  have n₃ : N ≫ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]) =
      (lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ := by
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, n₁, n₂, Category.assoc,
      Category.assoc, hκ]
  rw [← n₁, ← n₂, ← n₃]
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ hw N.left).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))

theorem weight_box₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → ∀ (κ : splitTorus S D.X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (κ₂ : splitTorus S D₂.X ⟶ G₂) (j₁ : D₁.X → D.X) (j₂ : D₂.X → D.X) (τ₁ : splitTorus S D.X ⟶ splitTorus S D₁.X) (τ₂ : splitTorus S D.X ⟶ splitTorus S D₂.X), j₁ (q₁ χ) + j₂ (q₂ χ) = χ → TorusHomOf j₁ τ₁ → TorusHomOf j₂ τ₂ → κ ≫ σ₁ = τ₁ ≫ κ₁ → κ ≫ σ₂ = τ₂ ≫ κ₂ → (Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ P = (Over.map s).map (snd (splitTorus S D.X) G) ≫ P → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left) (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L (q₁ χ)) (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (lift (fst (splitTorus S D₂.X) G₂ ≫ κ₂) (snd _ _) ≫ μ[G₂]).left) (LB.mulGen D₂.P.L _ _ _ _ (charGen D₂.X G₂ D₂.P.L (q₂ χ)) (LB.pullGen D₂.P.L _ _ t₂ (snd (splitTorus S D₂.X) G₂).left)) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left) (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L χ) (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ hσ₁ hσ₂ H κ κ₁ κ₂ j₁ j₂ τ₁ τ₂ hχ
    hτ₁ hτ₂ hκ₁ hκ₂ aO hw₁ hw₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v₁ := val_weight σ₁ t₁ κ κ₁ τ₁ hκ₁ hw₁ y hJ₁
  have v₂ := val_weight σ₂ t₂ κ κ₂ τ₂ hκ₂ hw₂ y hJ₂
  rw [gm_char_hom hτ₁] at v₁
  rw [gm_char_hom hτ₂] at v₂
  have c := gm_char_add (fst (splitTorus S D.X) G) y (j₁ (q₁ χ)) (j₂ (q₂ χ))
  rw [hχ] at c
  have b₁ := H _ (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := H _ (snd (splitTorus S D.X) G).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have e : ∀ a, (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a =
      (snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a := fun a =>
    (WeightPf.Oφ_comp ((Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G])) P χ a).trans
      ((congrArg (fun m => D.Oφ m χ a) aO).trans
        (WeightPf.Oφ_comp ((Over.map s).map (snd (splitTorus S D.X) G)) P χ a).symm)
  have o : (∏ a, om w y J₁ J₂ J ((lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a) ^ Oinvε a) =
      ∏ a, om w y J₁ J₂ J ((snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a) ^ Oinvε a :=
    Finset.prod_congr rfl fun a _ => congrArg (fun m => om w y J₁ J₂ J m ^ Oinvε a) (e a)
  have v₄ := (congrArg₂ (· * ·) o rfl).symm.trans (b₁.trans ((congrArg₂ (· * ·) v₁ v₂).trans
    ((_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg₂ (· * ·) c.symm b₂.symm).trans (mul_left_comm _ _ _)))))
  have v₅ := mul_left_cancel v₄
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅

end GlobalTheory.ProdUnifWeight
