import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifUnit

theorem prod_unit {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T₀ : Over (Sp R)} (r : T₀ ⟶ T)
    (P : T ⟶ D.P.A) (h : r ≫ P = 1) (χ : D.X) {U : Type} [CommGroup U] (f : (T₀.left ⟶ D.P.A.left) → U) :
    ∏ k, f (r.left ≫ D.Oφ P χ k) ^ Oinvε k = 1 := by
  have e : ∀ k, r.left ≫ D.Oφ P χ k = D.Oφ (1 : T₀ ⟶ D.P.A) χ k := fun k => by
    rw [← h]; exact (WeightPf.Oφ_comp r P χ k).trans rfl
  have e₀ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 0 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 1 :=
    congrArg (fun m : T₀ ⟶ D.P.A => m.left) (_root_.one_mul (toUnit T₀ ≫ D.c χ))
  have e₂ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 2 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 3 := rfl
  simp only [e]
  rw [Fin.prod_univ_four, e₀, e₂]
  simp [Oinvε]

theorem unit_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → (Over.map s).map η[G] ≫ P = 1 → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (eSec G₁)) (LB.oneGen D₁.P.L) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (eSec G₂)) (LB.oneGen D₂.P.L) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec G)) (LB.oneGen D.P.L) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ h₁ h₂ H e u₁ u₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v := H _ (eSec G) y J₁ J₂ J hJ₁ hJ₂ hJ
  have o := prod_unit D ((Over.map s).map η[G]) P e χ (om w y J₁ J₂ J)
  have a₁ : eSec G ≫ σ₁.left = 𝟙 _ ≫ eSec G₁ := (SumDeg.eSec_comp σ₁).trans (Category.id_comp _).symm
  have a₂ : eSec G ≫ σ₂.left = 𝟙 _ ≫ eSec G₂ := (SumDeg.eSec_comp σ₂).trans (Category.id_comp _).symm
  have b₁ : val t₁ (eSec G ≫ σ₁.left) y J₁ = 1 := (congrArg (fun r => val t₁ r y J₁) a₁).trans
    ((val_pull hJ₁ _ _ _).symm.trans ((val_corr hJ₁ u₁ (𝟙 _)).trans (val_one _)))
  have b₂ : val t₂ (eSec G ≫ σ₂.left) y J₂ = 1 := (congrArg (fun r => val t₂ r y J₂) a₂).trans
    ((val_pull hJ₂ _ _ _).symm.trans ((val_corr hJ₂ u₂ (𝟙 _)).trans (val_one _)))
  have c : val t (eSec G) y J = 1 :=
    ((congrArg₂ (· * ·) o rfl).trans (_root_.one_mul _)).symm.trans
      (v.trans ((congrArg₂ (· * ·) b₁ b₂).trans (_root_.one_mul _)))
  exact (val_pull hJ _ _ _).trans ((congrArg (fun r => val t r y J) (Category.id_comp _)).trans
    (c.trans (val_one _).symm))

end GlobalTheory.ProdUnifUnit
