import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem dualMap_injective_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (Formalism.L2.Pj.dualMap f) := by
  intro a b h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [Formalism.L2.Pj.dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at h1 h2
  exact TrivSqZeroExt.ext (hf h1) (hf h2)

theorem intData_models_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I I' : IntData Xo c T io y), ∃ n : SABMap I.G I'.G (𝟙 (Sp T.V)), ∀ τ i, (I.ub τ i).left ≫ n.φ = (I'.ub τ i).left := by
  intro E _ _ _ H Dw l Xo c T io y I I'
  letI := io.toAlgebra
  obtain ⟨k, n, hk, hn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr y.x I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2
  refine ⟨n, fun τ i => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := I.lift τ i
  obtain ⟨v, hv1, hv2⟩ := I'.lift τ i
  have hnw : n.φ ≫ I'.G.G.hom = I.G.G.hom := n.cart.1.w.trans (Category.comp_id _)
  have hkw : k.φ ≫ I'.t'.G.hom = I.t'.G.hom := k.cart.1.w.trans (Category.comp_id _)
  have huv : u ≫ k.φ = v := by
    apply I'.m1.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (u ≫ ·) hk).trans (hu1.trans hv1.symm)
    · rw [Category.assoc, hkw]
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      have e1 : (u ≫ I.m2.φ) ≫ I.G.G.hom = (v ≫ I'.m2.φ) ≫ I'.G.G.hom := by
        rw [hu2, hv2, Category.assoc, Category.assoc, Over.w (I.ub τ i), Over.w (I'.ub τ i)]
      rw [Category.assoc, Category.assoc, ← I.m2.cart.1.w, ← I'.m2.cart.1.w]
      simpa only [Category.assoc] using e1
  have hsep : IsSeparated I'.G.G.hom := I'.G.semi.separated
  have hdom : IsSchemeTheoreticallyDominant (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom _)
      (dualMap_injective_of_injective _ (IsFractionRing.injective T.V T.Fr))
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant I'.G.G.hom ?_ (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) ?_
  · rw [Category.assoc, hnw, Over.w (I.ub τ i), Over.w (I'.ub τ i)]
  · rw [← Category.assoc, ← hu2, ← hv2, Category.assoc, hn, ← Category.assoc, huv]

end GlobalTheory.ChartCmp
