import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_gen_isoLB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  have hL₁ : Z.o₁.t.PP.L.IsLB := Z.o₁.t.PP.isLB
  have hL₂ : Z.o₂.t.PP.L.IsLB := Z.o₂.t.PP.isLB
  obtain ⟨w₁, hw₁, -⟩ := Z.m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := Z.m₂.lin
  have i₁ : LBIso Z.o₁.t.PP.L (Xo.univ.t.PP.L.pull Z.m₁.cm.F) := ⟨w₁, hw₁⟩
  have i₂ : LBIso Z.o₂.t.PP.L (Xo.univ.t.PP.L.pull Z.m₂.cm.F) := ⟨w₂, hw₂⟩
  have i₃ : LBIso (lbPow Z.o₁.t.PP.L (p ^ 2)) (Xo.univ.t.PP.L.pull (Z.ψ.left ≫ Z.m₂.cm.F)) :=
    GlobalTheory.ThetaAffineGlue.lbIso_comp (isLB_lbPow hL₁ _) hL₂ hL Z.isog.1.2.2.2.2.2 i₂
  have i₄ := GlobalTheory.ThetaAffineGlue.lbIso_pull i₃ (hkLift Z h hx)
  have i₅ := GlobalTheory.Spread.lbIso_pow_pull_comp hL hL₁ i₁ (hkLift Z h hx) (hkLift_φ Z hx).symm (p ^ 2)
  have i₆ := lbIso_lbPow_pull hL₁ (hkLift Z h hx) (p ^ 2)
  have i₇ := GlobalTheory.EmbVA.lbIso_pow hL (snd (Over.mk x) Xo.univ.t.G).left (p ^ 2) ((p : ℤ) ^ 2) (by push_cast; rfl)
  have i₈ := ((i₇.trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL _) _)
    (isLB_lbPow (pull_isLB hL₁ _) _) i₅.symm).trans (LB.isLB_linComb hL _ _) (isLB_lbPow (pull_isLB hL₁ _) _)
    (pull_isLB (isLB_lbPow hL₁ _) _) i₆).trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL₁ _) _)
    (pull_isLB hL _) i₄
  have e := (GlobalTheory.PrimNorm.lbIso_iff hL _ _ _ _).1 i₈
  rw [Fin.prod_univ_one, Fintype.prod_unique, zpow_one] at e
  refine (GlobalTheory.PrimNorm.hasGen_iff hL (isoφ Xo.univ.t.G (hkMap Z hx hx')) ![(p : ℤ) ^ 2, -1]).2 ?_
  rw [prod_iso', hkMap_snd, e, mul_inv_cancel]

end GlobalTheory.HeckeEx
