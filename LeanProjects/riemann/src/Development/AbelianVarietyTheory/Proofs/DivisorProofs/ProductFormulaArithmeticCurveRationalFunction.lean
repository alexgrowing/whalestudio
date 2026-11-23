import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteIntStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveFinsumOrdLogEqLocalLengthsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveSumComplexPointsLogEqRingHoStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveProd

theorem product_formula_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  intro k _ Y _ _ q hq f hf
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int k Y q hq
  have := hAff
  have := hFin
  have : Module.Finite ℤ k := hq.finite
  have hgen : genericPoint Y ∈ (⊤ : Y.Opens) := trivial
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : CharZero Γ(Y, ⊤) := (flat_int_iff_charZero (q ≫ spMap (Int.castRingHom k))).1 hq.flat
  have : IsFractionRing Γ(Y, ⊤) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)

  have finHom : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], Finite (B →+* ℂ) := by
    intro B _ _
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
    have hint : ∀ x : B, IsIntegral ℤ x := fun x => Algebra.IsIntegral.isIntegral x
    choose p hpm hp using hint
    let T : Set (s → ℂ) :=
      Set.pi Set.univ fun x => {z : ℂ | ((p x).map (Int.castRingHom ℂ)).IsRoot z}
    have hT : T.Finite :=
      Set.Finite.pi fun x => Polynomial.finite_setOfPred_isRoot ((hpm x).map _).ne_zero
    have hmem : ∀ φ : B →+* ℂ, (fun x : s => φ x) ∈ T := by
      intro φ x _
      show Polynomial.eval (φ (x : B)) ((p x).map (Int.castRingHom ℂ)) = 0
      rw [Polynomial.eval_map]
      rw [← show φ.comp (algebraMap ℤ B) = Int.castRingHom ℂ from RingHom.ext_int _ _,
        ← Polynomial.hom_eval₂, hp x, map_zero]
    let F : (B →+* ℂ) → T := fun φ => ⟨fun x => φ x, hmem φ⟩
    have hF : Function.Injective F := by
      intro φ ψ h
      have h' : Set.EqOn φ.toAddMonoidHom.toIntLinearMap ψ.toAddMonoidHom.toIntLinearMap (s : Set B) := by
        intro x hx
        have := congrArg (fun t : T => t.1 ⟨x, hx⟩) h
        simpa [F] using this
      have hl := LinearMap.ext_on hs h'
      ext x
      exact LinearMap.congr_fun hl x
    have : Finite T := hT.to_subtype
    exact Finite.of_injective F hF

  have finZero : ∀ c : Γ(Y, ⊤), Finite (Γ(Y, ⊤) ⧸ Ideal.span {c}) →
      {z : Y | z ∉ Y.basicOpen c}.Finite := by
    intro c _
    have hS : (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {c})))).Finite :=
      Set.finite_range _
    refine (hS.preimage fun _ _ _ _ h => Y.toSpecΓ.isOpenEmbedding.injective h).subset ?_
    intro z hz
    have h1 : Y.toSpecΓ z ∉ PrimeSpectrum.basicOpen c := by
      intro h
      apply hz
      rw [← Scheme.toSpecΓ_preimage_basicOpen]
      exact h
    show Y.toSpecΓ z ∈ Set.range _
    apply (Set.ext_iff.1 (range_comap_of_surjective _ (Ideal.Quotient.mk (Ideal.span {c}))
      Ideal.Quotient.mk_surjective) _).2
    have h2 : c ∈ (Y.toSpecΓ z).asIdeal := by
      by_contra h
      exact h1 h
    rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff.2 h2

  have hgb : ∀ c : Γ(Y, ⊤), c ≠ 0 → genericPoint Y ∈ Y.basicOpen c := by
    intro c hc
    by_contra h
    apply hc
    rw [← basicOpen_eq_bot_iff (X := Y) (U := ⊤) c, ← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
    rintro ⟨x, hx⟩
    exact h (gen_mem hx)

  have hsupp : ∀ c : Γ(Y, ⊤), c ≠ 0 → (Function.support fun z =>
      (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
        Real.log (Nat.card (Y.residueField z))).Finite := by
    intro c hc
    refine (finZero c (GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc).1).subset ?_
    intro z hz hzc
    apply hz
    have hu : UnitAt z (algebraMap Γ(Y, ⊤) Y.functionField c) :=
      (unitAt_fnOf_iff (U := ⊤) trivial hgen c).2 hzc
    simp only
    rw [hu.ord_eq_zero]
    simp

  have key : ∀ c : Γ(Y, ⊤), c ≠ 0 →
      ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) =
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField c) y‖ := by
    intro c hc
    obtain ⟨hfq, hlog⟩ := GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc
    have := hfq
    rw [GlobalTheory.T.affineArithmeticCurve_finsum_ord_log_eq_localLengths k Y q hq c hc, ← GlobalTheory.T.log_card_eq_finsum_length_localized_maximal Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ Ideal.span {c}), hlog,
      GlobalTheory.T.affineArithmeticCurve_sum_complexPoints_log_eq_ringHoms k Y q hq c]

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Γ(Y, ⊤) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hf
  have hinj := IsFractionRing.injective Γ(Y, ⊤) Y.functionField
  have ha'0 : algebraMap Γ(Y, ⊤) Y.functionField a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb'0 : algebraMap Γ(Y, ⊤) Y.functionField b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hord : ∀ z, Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z =
        Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z -
          Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z := by
    intro z
    have h := Scheme.ord_mul (x := z) (div_ne_zero ha'0 hb'0) hb'0
    rw [div_mul_cancel₀ _ hb'0] at h
    omega

  have hpt : ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖ -
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    intro σ y
    have hg : under y = genericPoint Y := GlobalTheory.TwistTop.under_eq_genericPoint hq y
    have hua : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen a).2 (hgb a ha0)
    have hub : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen b).2 (hgb b hb0)
    have huq : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [div_eq_mul_inv]
      exact hua.mul hub.inv
    have hm : ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y =
        ratVal (algebraMap Γ(Y, ⊤) Y.functionField a / algebraMap Γ(Y, ⊤) Y.functionField b) y *
          ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y := by
      rw [← ratVal_mul huq.regAt hub.regAt, div_mul_cancel₀ _ hb'0]
    rw [hm, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero huq))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hub))]
    ring
  have hL : ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) =
      (∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z : ℝ) *
          Real.log (Nat.card (Y.residueField z))) -
        ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) := by
    rw [← finsum_sub_distrib (hsupp a ha0) (hsupp b hb0)]
    refine finsum_congr fun z => ?_
    rw [hord z]
    push_cast
    ring
  have hR : ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
      (∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖) -
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    have : Finite (k →+* ℂ) := finHom k
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun σ => ?_
    have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun y => hpt σ y
  rw [hL, hR, key a ha0, key b hb0]

end GlobalTheory.CurveProd
