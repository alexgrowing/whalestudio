import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelCompat

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem thickMap_fstG {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem mono_fstG {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

noncomputable def thickMapOver {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
      (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    rw [← Over.w (fstG I (e + 1) G), ← Over.w (fstG I e G), ← thickMap_fstG I e G]
    exact (Category.assoc _ _ _).symm)

theorem thickMap_Oφ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g₀ : GtCoord I D e G)
    (g₁ : GtCoord I D (e + 1) G) (hq : thickMap R I e G ≫ g₁.pG.left = g₀.pG.left) (χ : D.X) (k : Fin 4) :
    thickMap R I e G ≫ D.Oφ g₁.pG χ k = D.Oφ g₀.pG χ k := by
  have h : thickMapOver I e G ≫ g₁.pG = g₀.pG := Over.OverMorphism.ext hq
  rw [← h]
  exact WeightPf.Oφ_comp (thickMapOver I e G) g₁.pG χ k

theorem corr_of_pmaps {X X' Y₀ Y₁ Y₀' Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ₀ : K → (Y₀ ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₀' : K → (Y₀' ⟶ X')} {φ₁' : K → (Y₁' ⟶ X')}
    {t₀ : LB.Gen (LB.LinComb L φ₀ ε)} {t₁ : LB.Gen (LB.LinComb L φ₁ ε)}
    {t₀' : LB.Gen (LB.LinComb L' φ₀' ε)} {t₁' : LB.Gen (LB.LinComb L' φ₁' ε)}
    {h₀ : Y₀' ⟶ Y₀} {h₁ : Y₁' ⟶ Y₁} {m : Y₀ ⟶ Y₁} {m' : Y₀' ⟶ Y₁'} (hm : m' ≫ h₁ = h₀ ≫ m)
    (c₀ : ∀ k, φ₀' k ≫ F = h₀ ≫ φ₀ k) (c₁ : ∀ k, φ₁' k ≫ F = h₁ ≫ φ₁ k) (c' : ∀ k, m' ≫ φ₁' k = φ₀' k)
    (H₀ : PMaps w φ₀' φ₀ ε t₀' t₀ h₀) (H₁ : PMaps w φ₁' φ₁ ε t₁' t₁ h₁)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t₁ m) t₀) :
    LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ t₁' m') t₀' := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  choose J hJ using fun χ : Y₀' ⟶ X => exists_chart hL (χ y)
  have hJ : Good L y J := hJ
  rw [val_pull hJ', Category.id_comp]
  have a₀ := H₀ _ (𝟙 _) y (fun k => J (φ₀' k ≫ F)) (fun k => J' (φ₀' k)) (fun k => hJ (φ₀' k ≫ F))
    (fun k => hJ' (φ₀' k))
  have a₁ := H₁ _ m' y (fun k => J (φ₀' k ≫ F)) (fun k => J' (φ₀' k))
    (fun k => (congrArg (fun g => F (g y) ∈ L.U (J (φ₀' k ≫ F))) (c' k)).mpr (hJ (φ₀' k ≫ F)))
    (fun k => (congrArg (fun g => g y ∈ L'.U (J' (φ₀' k))) (c' k)).mpr (hJ' (φ₀' k)))
  rw [← val_of t₀ _ y J _ (fun k => by rw [Category.id_comp, c₀]),
    ← val_of t₀' _ y J' _ (fun k => by rw [Category.id_comp]), Category.id_comp] at a₀
  rw [← val_of t₁ _ y J _ (fun k => by rw [Category.assoc, ← c₁, ← Category.assoc, c']),
    ← val_of t₁' _ y J' _ (fun k => by rw [c']), hm, ← val_pull hJ, val_corr hJ H, a₀] at a₁
  simp only [Category.id_comp, c'] at a₁
  exact (mul_left_cancel a₁).symm

end LevelCompat

open LevelCompat in

theorem gtCoord_compat_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (e : ℕ) (g₀ : GtCoord I D e G) (g₁ : GtCoord I D (e + 1) G) (g₀' : GtCoord I' D' e G') (g₁' : GtCoord I' D' (e + 1) G') (h₀ : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (h₁ : (thickObj R' I' (e + 1) G').left ⟶ (thickObj R I (e + 1) G).left), h₀ ≫ (fstG I e G).left = (fstG I' e G').left ≫ Ψ → h₁ ≫ (fstG I (e + 1) G).left = (fstG I' (e + 1) G').left ≫ Ψ → ((g₀').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ (g₀).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₀').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ D.Oφ (g₀).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₀').pG x) (D.Oφ (g₀).pG (hD.xe x)) Oinvε ((g₀').t x) ((g₀).t (hD.xe x)) h₀) → ((g₁').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ (g₁).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₁').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ D.Oφ (g₁).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₁').pG x) (D.Oφ (g₁).pG (hD.xe x)) Oinvε ((g₁').t x) ((g₁).t (hD.xe x)) h₁) → thickMap R I e G ≫ g₁.pG.left = g₀.pG.left → (∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g₁.t χ) (thickMap R I e G)) (g₀.t χ)) → thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left ∧ ∀ χ : D'.X, LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ (g₁'.t χ) (thickMap R' I' e G')) (g₀'.t χ) := by
  intro R R' _ _ _ _ φ D D' hD I I' G _ _ G' _ _ Ψ e g₀ g₁ g₀' g₁' h₀ h₁ hh₀ hh₁ ⟨p₀, H₀⟩ ⟨p₁, H₁⟩ hq ht
  have hm : thickMap R' I' e G' ≫ h₁ = h₀ ≫ thickMap R I e G := by
    have := mono_fstG I (e + 1) G
    rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hh₁, thickMap_fstG, hh₀,
      ← thickMap_fstG I' e G']
    exact (Category.assoc _ _ _).symm
  have hq' : thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left := by
    have h : (thickMapOver I' e G' ≫ g₁'.pG) ≫ hD.e.hom = g₀'.pG ≫ hD.e.hom := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · show ((thickMap R' I' e G' ≫ g₁'.pG.left) ≫ hD.e.hom.left) ≫ _ = (g₀'.pG.left ≫ hD.e.hom.left) ≫ _
        simp only [Category.assoc]
        exact (congrArg (thickMap R' I' e G' ≫ ·) p₁).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ g₁.pG.left) hm).trans ((Category.assoc _ _ _).trans
          ((congrArg (h₀ ≫ ·) hq).trans p₀.symm))))
      · exact (Over.w _).trans (Over.w _).symm
    exact congrArg (fun z => z.left) ((cancel_mono hD.e.hom).1 h)
  exact ⟨hq', fun χ => corr_of_pmaps D.P.isLB D'.P.isLB hD.w hm (H₀ χ).1 (H₁ χ).1
    (thickMap_Oφ g₀' g₁' hq' χ) (H₀ χ).2 (H₁ χ).2 (ht _)⟩

end GlobalTheory
