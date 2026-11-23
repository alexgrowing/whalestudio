import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.twistRatio_eq_one_at_unit : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X) (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) ae) (LB.pullGen D.P.L _ _ (gp.s χ) (thick R I e))) → ∀ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (J : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D.P.A.left) → D.P.L.ι) (J' : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val (g.t χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ h) z J * ((∏ k, gv w ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J (((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J' * val (gp.s χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = 1 := by
  intro R _ _ I D D₂ e G _ _ g g₂ β gp w χ₂ χ a h hh hf hcorr z J J' hJ hJ'
  set o := (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G) with ho
  have hom1 : o.left ≫ (thickObj R I e G).hom = 𝟙 _ := Over.w o
  have e1 : o.left ≫ h ≫ (thickObj R I e G).hom = 𝟙 _ := by rw [hh, hom1]
  have f1 : (Over.map (thick R I e)).map o ≫ fstG I e G = 1 := by
    have := GlobalTheory.FormalPoint.map_mul_fstG (R := R) (I := I) (e := e) (G := G) o o
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  let T := (Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))))
  have tu : (toUnit T).left = thick R I e := by
    have := Over.w (toUnit T)
    simpa [T] using this
  have e2 : o.left ≫ h ≫ (fstG I e G).left = thick R I e ≫ a.left := by
    rw [hf]
    show ((Over.map (thick R I e)).map o ≫ fstG I e G ≫ ((toUnit G ≫ a) * 𝟙 G)).left = _
    rw [← Category.assoc, f1, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, _root_.mul_one,
      Over.comp_left, tu]
  have hc := hcorr (o.left ≫ h) (by simpa [Category.assoc] using e1) (by simpa [Category.assoc] using e2)
  have va := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at va
  have vb : val (g₂.t χ₂) o.left z J' = 1 := GlobalTheory.TorusCoord.val_unit g₂ χ₂ hJ'
  let f : (_ ⟶ D₂.P.A.left) → _ := fun ψ => gv w ψ z (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ψ)
  have e0 : ∀ k, o.left ≫ D₂.Oφ g₂.pG χ₂ k = D₂.Oφ (1 : T ⟶ D₂.P.A) χ₂ k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R I e)).map o) g₂.pG χ₂ k).trans
      (congrArg (D₂.Oφ · χ₂ k) (GlobalTheory.TorusCoord.im_one g₂))
  have vc : (∏ k, f (o.left ≫ D₂.Oφ g₂.pG χ₂ k) ^ Oinvε k) = 1 := by
    refine (Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_
    rw [Fin.prod_univ_four]
    show f ((1 : T ⟶ D₂.P.A) * (toUnit T ≫ D₂.c χ₂)).left ^ (-1 : ℤ) * f (toUnit T ≫ D₂.c χ₂).left ^ (1 : ℤ) *
      f (1 : T ⟶ D₂.P.A).left ^ (1 : ℤ) * f (1 : T ⟶ D₂.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have vc' : (∏ k, gv w (o.left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((o.left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (o.left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) = 1 := vc
  rw [vc', vb, ← Category.assoc, hom1, Category.id_comp, va, _root_.one_mul, _root_.one_mul, mul_inv_cancel]
