import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GtCoeff

theorem exists_coeff_gt : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))), t.IsGen → ∀ (k : ℕ) (α : D.X) (s : D.SecB k α), ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval s (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z a * (val (L := D.P.L) D.rig r z J ^ k).val := by
  intro R _ _ D g t ht k α s
  have key := ExpansionValueZero.exists_coeff (A := R) D.P.isLB s g.b.left
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.s α))
      (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ t k))) (GeneratorPullback.powGen D.P.L _ _ D.rig k))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (g.isGen α))
      (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ ht k))) (powGen_isGen _ _ _ _ D.rig_gen k))
  obtain ⟨a, ha⟩ := key (by
    have e1 : g.b.left ≫ D.famφB α 1 = D.gtφT (𝟙_ _) g.b α 0 := by
      show g.b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A (DegPre.cT D _ α) g.b).left
      rw [← Over.comp_left]
      congr 1
      change g.b ≫ ((𝟙 _) * (toUnit _ ≫ D.c α)) = (toUnit _ ≫ D.c α) * g.b
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, mul_comm]
    have e2 : g.b.left ≫ D.famφB α 2 = D.gtφT (𝟙_ _) g.b α 1 := by
      show g.b.left ≫ (toUnit D.P.A ≫ D.c α).left = (toUnit _ ≫ D.c α).left
      rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    have e3 : g.b.left ≫ D.famφB α 3 = eSec D.P.A := by
      show g.b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = η[D.P.A].left
      rw [← Over.comp_left, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    have e0 : g.b.left ≫ D.famφB α 0 = g.b.left := Category.comp_id _
    have g3 : D.gtφT (𝟙_ _) g.b α 3 = eSec D.P.A := by
      show (toUnit (𝟙_ (Over (Sp R))) ≫ η[D.P.A]).left = η[D.P.A].left
      rw [toUnit_unit, Category.id_comp]
    have g2 : D.gtφT (𝟙_ _) g.b α 2 = g.b.left := rfl
    have l0 : (![(η[D.P.A]).left, g.b.left] : Fin 2 → (Sp R ⟶ D.P.A.left)) 0 = eSec D.P.A := rfl
    have l1 : (![(η[D.P.A]).left, g.b.left] : Fin 2 → (Sp R ⟶ D.P.A.left)) 1 = g.b.left := rfl
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr]
    rw [e0, e1, e2, e3, g2, g3, l0, l1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, DegPre.famε, DegPre.gtε, DegPre.lineε, Matrix.cons_val]
    module)
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [ha Z r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pow, val_pow, _root_.mul_assoc, _root_.mul_assoc,
    ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [mul_comm, _root_.mul_assoc, mul_left_comm, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel, inv_mul_cancel, _root_.mul_one]

end GlobalTheory.GtCoeff
