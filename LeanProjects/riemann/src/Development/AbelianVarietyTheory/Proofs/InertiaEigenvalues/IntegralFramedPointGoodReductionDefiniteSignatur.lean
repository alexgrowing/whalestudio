import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.DefiniteAbelian
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem abLocus_eq_univ_of_definite (Xo : Moduli Dw l) (hq : Dw.q = 0) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X)
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : abLocus G.G = Set.univ := by
  obtain ⟨m, hm, hw⟩ := exists_w0_relation H
  obtain ⟨b, hb⟩ := Spec.map_surjective (x ≫ Xo.s)
  let β : KA l →+* T.Fr := b.hom
  have hβ : x ≫ Xo.s = spMap β := hb.symm
  have : CharZero T.Fr := (RingHom.charZero_iff β.injective).1 inferInstance
  let ρ : T.Fr := β (baseKA l).ρ
  have hρ : ρ ^ 2 = -(H.d : T.Fr) := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hm' : (4 : T.Fr) * m = 1 + H.d := by exact_mod_cast hm
  let z : T.Fr := (1 + ρ) / 2
  have hz2 : 2 * z = 1 + ρ := mul_div_cancel₀ _ two_ne_zero
  have hz : z * z + m = z := mul_left_cancel₀ (show (4 : T.Fr) ≠ 0 by norm_num) (by
    linear_combination (2 * z + ρ - 1) * hz2 + hρ + hm')
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : T.V, algebraMap T.V T.Fr z₀ = z := by
    rcases ValuationRing.isInteger_or_isInteger T.V z with h | ⟨u, hu⟩
    · exact h
    · by_cases h0 : z = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · refine ⟨1 - m * u, ?_⟩
        rw [map_sub, map_one, map_mul, map_natCast, hu]
        field_simp
        linear_combination -hz
  let L := AlgebraicClosure T.Fr
  let a : T.Fr →+* L := algebraMap T.Fr L
  have : CharZero L := (RingHom.charZero_iff a.injective).1 inferInstance
  have hdet := (Xo.univ.geom L (spMap a ≫ x) (a.comp β) (by rw [Category.assoc, hβ, sp_comp])).1
  have h₁ := actsBy_of_detCond Dw hq _ (spMap a ≫ x) _ (a z)
    (by rw [← map_ofNat a 2, ← map_mul, hz2, map_add, map_one]; rfl) hdet
  have h₂ := (actsBy_pull m₂.cart (m₂.act H.w0) (spMap a) _).1 ((actsBy_pull m₁.cart (m₁.act H.w0) (spMap a) _).2 h₁)
  have := G.semi.smooth
  have := G.semi.separated
  have := G.act.hom H.w0
  have h₃ : ActsBy G.G (G.act.act H.w0) (𝟙 _) z₀ := by
    refine actsBy_of_injective (a.comp (algebraMap T.V T.Fr))
      (a.injective.comp (IsFractionRing.injective T.V T.Fr)) _ _ ?_
    rw [Category.comp_id, ← sp_comp, RingHom.comp_apply, hz₀]
    exact h₂
  refine Set.eq_univ_of_forall fun p K _ _ t _ => ?_
  obtain ⟨j, hj⟩ := Spec.map_surjective t
  have h₄ := actsBy_baseChange (k := K) j.hom (𝟙 _) _ h₃
  have ht : spMap j.hom ≫ 𝟙 _ = t := (Category.comp_id _).trans hj
  rw [ht] at h₄
  obtain ⟨X⟩ := G.semi.fibres K t
  exact isProper_of_actsBy X (OAct.pullback t G.G G.act) H.d_prime hm hw _
    ((actsBy_pull (isGrpPullback_pullback G.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))

theorem good_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  intro E _ _ _ H Dw l Xo c hq T io y
  obtain ⟨G, t', m₁, m₂, -⟩ := y.2.2
  exact ⟨G, t', m₁, m₂, GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H Dw l Xo T _ G t' m₁ m₂
    (abLocus_eq_univ_of_definite Xo hq T _ G t' m₁ m₂)⟩

end GlobalTheory.GoodDefinite
