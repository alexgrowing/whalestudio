import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIso
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
namespace GlobalTheory.MumCmp.TranslRatio

theorem prod_gtφT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h ((toUnit T' ≫ D.c χ) * (ρ ≫ b)).left)⁻¹ * h (toUnit T' ≫ D.c χ).left * h (ρ ≫ b).left *
        (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, ← comp_toUnit ρ, Category.assoc, ← MonObj.comp_mul, ← MonObj.comp_one ρ]
  show h (ρ ≫ ((toUnit T ≫ D.c χ) * b)).left ^ (-1 : ℤ) * h (ρ ≫ toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h (ρ ≫ b).left ^ (1 : ℤ) * h (ρ ≫ (1 : T ⟶ D.P.A)).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem formEq_translate {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R)
    {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (hT : T ⟶ T) (p : T ⟶ D.P.A)
    (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (hp : hT ≫ p = (p₂ ≫ β) * (toUnit T ≫ b)) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => hT.left ≫ D.Oφ p χ k)
        (Sum.elim (fun k : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2)
          (fun k => (toUnit T).left ≫ DegPre.gtφT D _ b χ k)))
      (Sum.elim Oinvε (fun k => - Sum.elim (fun k : Fin 4 × Fin 3 => Oinvε k.1 * twε k.2) DegPre.gtε k))
      (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D.c χ) (D.c χ) k) ![1, -1, 1, -1] := by
  intro U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ twφ D₂ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k =
      ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ k : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2) ^ (Oinvε k.1 * twε k.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] :
        Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β * (toUnit T ≫ b) =
      (p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.assoc, hc, mul_right_comm]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (hT.left ≫ D.Oφ p χ k) ^ (Oinvε k) =
      (h ((p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h ((p₂ ≫ β) * (toUnit T ≫ b)).left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
    simp only [WeightPf.Oφ_comp]
    rw [Fin.prod_univ_four, ← hp]
    show h ((hT ≫ p) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (hT ≫ p).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
    simp only [zpow_neg, zpow_one]
  have hS : ∏ k, h ((toUnit T).left ≫ DegPre.gtφT D _ b χ k) ^ (DegPre.gtε k) =
      (h ((toUnit T ≫ D.c χ) * (toUnit T ≫ b)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h (toUnit T ≫ b).left * (h (1 : T ⟶ D.P.A).left)⁻¹ :=
    prod_gtφT (toUnit T) b χ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, hC, hS, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, h0, h3, _root_.one_mul, Category.assoc, hc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio_gen : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)), w.IsGen → ∀ (χ₂ : D₂.X) (χ : D.X), D₂.c χ₂ ≫ β = D.c χ → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ g.pG.left = g₂.pG.left ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b 0 → ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ GlobalTheory.CoordCompare.diffφ (D.prBe I e) (D.c χ) (D.c χ) k) ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val u r z J = val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ gp w hw χ₂ χ hc h hh hp
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let hT : T ⟶ T := Over.homMk h ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) hh))
  obtain ⟨t₁, ht₁, hv₁⟩ := GlobalTheory.Mum.GenTransport.exists_transport D.P.isLB D₂.P.isLB _ _ w hw _ _
    (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_translate D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) hT g.pG g₂.pG β gp.b
    (Over.OverMorphism.ext hp |>.trans (by
      show g₂.pG ≫ (β * (toUnit D₂.P.A ≫ gp.b)) = _
      rw [MonObj.comp_mul, comp_toUnit_assoc])) χ₂ χ hc
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) h) (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L _ _ (gp.s χ) ((thickObj R I e G).hom ≫ thick R I e)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ (DVR.pullGen_isGen _ _ _ _ (gp.isGen χ) _))))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r)
    ((val_inv _ r).trans (congrArg (·⁻¹) ((val_mul hJ _ _ r).trans
      (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r)))))))

end GlobalTheory.MumCmp.TranslRatio
