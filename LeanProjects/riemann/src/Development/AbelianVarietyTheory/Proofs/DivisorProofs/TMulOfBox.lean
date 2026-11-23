import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

theorem tMul_of_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), IsBoxGen (φ := thφ D.P.A (x3 D.P.A)) (φ₁ := thφ D₁.P.A (x3 D₁.P.A)) (φ₂ := thφ D₂.P.A (x3 D₂.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t → ∀ (T T₁ T₂ : Over (Sp R)) (P : T ⟶ D.P.A) (P₁ : T₁ ⟶ D₁.P.A) (P₂ : T₂ ⟶ D₂.P.A) (ρ₁ : T ⟶ T₁) (ρ₂ : T ⟶ T₂), P ≫ p₁ = ρ₁ ≫ P₁ → P ≫ p₂ = ρ₂ ≫ P₂ → ∀ (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : ∀ χ : D₁.X, LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ χ) Oinvε)) (t₂ : ∀ χ : D₂.X, LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ χ) Oinvε)), (∀ x, IsBoxGen w ρ₁.left ρ₂.left (t x) (t₁ (q₁ x)) (t₂ (q₂ x))) → TMul D₁ P₁ t₁ → TMul D₂ P₂ t₂ → TMul D P t := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hc T T₁ T₂ P P₁ P₂ ρ₁ ρ₂ e₁ e₂ t t₁ t₂ hb h₁ h₂ χ χ'
  haveI := hS.hom₁
  haveI := hS.hom₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have B : ∀ x, (om w y J₁ J₂ J (P * cP D T x).left)⁻¹ * om w y J₁ J₂ J (cP D T x).left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹ * val (t x) (𝟙 T.left) y J =
      val (t₁ (q₁ x)) ρ₁.left y J₁ * val (t₂ (q₂ x)) ρ₂.left y J₂ := fun x => by
    have := hb x T.left (𝟙 T.left) y J₁ J₂ J hJ₁ hJ₂ hJ
    simp only [Category.id_comp] at this
    rwa [GlobalTheory.TorusCoordPull.prod_O D P x (om w y J₁ J₂ J)] at this
  have K₁ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₁, cPoint_pr hS.c_pr₁, e₁, ← comp_cP D₁ ρ₁ (q₁ χ), ← comp_cP D₁ ρ₁ (q₁ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have K₂ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₂, cPoint_pr hS.c_pr₂, e₂, ← comp_cP D₂ ρ₂ (q₂ χ), ← comp_cP D₂ ρ₂ (q₂ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have C0 := hc T.left (lift (cP D T χ) (lift (cP D T χ') P)).left y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [K₁, K₂] at C0
  have pc := prod_cub (cP D T χ) (cP D T χ') P (om w y J₁ J₂ J)
  have C : (om w y J₁ J₂ J (cP D T χ * cP D T χ' * P).left * (om w y J₁ J₂ J (cP D T χ * cP D T χ').left)⁻¹ *
      (om w y J₁ J₂ J (cP D T χ * P).left)⁻¹ * (om w y J₁ J₂ J (cP D T χ' * P).left)⁻¹ *
      om w y J₁ J₂ J (cP D T χ).left * om w y J₁ J₂ J (cP D T χ').left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹) * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ := by
    rw [← pc]; exact C0
  have M₁ : val (t₁ (q₁ χ + q₁ χ')) ρ₁.left y J₁ *
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ =
      val (t₁ (q₁ χ)) ρ₁.left y J₁ * val (t₁ (q₁ χ')) ρ₁.left y J₁ := by
    have := (val_mul hJ₁ _ _ _).symm.trans ((val_corr hJ₁ (h₁ (q₁ χ) (q₁ χ')) ρ₁.left).trans (val_mul hJ₁ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm
  have M₂ : val (t₂ (q₂ χ + q₂ χ')) ρ₂.left y J₂ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ =
      val (t₂ (q₂ χ)) ρ₂.left y J₂ * val (t₂ (q₂ χ')) ρ₂.left y J₂ := by
    have := (val_mul hJ₂ _ _ _).symm.trans ((val_corr hJ₂ (h₂ (q₂ χ) (q₂ χ')) ρ₂.left).trans (val_mul hJ₂ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₂ _ _ _).symm
  have B0 := B (χ + χ')
  have Ba := B χ
  have Bb := B χ'
  rw [map_add, map_add, cPoint_add,
    show P * (cP D T χ * cP D T χ') = cP D T χ * cP D T χ' * P from mul_comm _ _] at B0
  rw [show P * cP D T χ = cP D T χ * P from mul_comm _ _] at Ba
  rw [show P * cP D T χ' = cP D T χ' * P from mul_comm _ _] at Bb
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans
    (congrArg (fun r => val D.cub.t r y J) (Category.id_comp _))))).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  show val (t (χ + χ')) (𝟙 T.left) y J * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
    val (t χ) (𝟙 T.left) y J * val (t χ') (𝟙 T.left) y J
  apply Additive.ofMul.injective
  have a0 := congrArg Additive.ofMul B0
  have a1 := congrArg Additive.ofMul Ba
  have a2 := congrArg Additive.ofMul Bb
  have a3 := congrArg Additive.ofMul C
  have a4 := congrArg Additive.ofMul M₁
  have a5 := congrArg Additive.ofMul M₂
  simp only [ofMul_mul, ofMul_inv] at a0 a1 a2 a3 a4 a5 ⊢
  linear_combination (norm := abel) a0 + a3 - a1 - a2 + a4 + a5

end GlobalTheory.ProdUnif
