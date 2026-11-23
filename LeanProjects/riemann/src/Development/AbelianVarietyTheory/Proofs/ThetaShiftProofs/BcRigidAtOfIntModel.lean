import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLetterRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstants
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointEqOfModelsOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isUnit_prod_det (Dw : Datum H) (L : Type) [Field L] : IsUnit (∏ τ, (letM Dw L τ).det) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcS Dw L) (arcDet Dw L)
  have e : algebraMap _ (ArcS Dw L) (arcDet Dw L) = ∏ τ, (letM Dw L τ).det := by
    exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun τ _ => RingHom.map_det _ _)
  exact e ▸ h

theorem exists_letterSub (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L)
    (N : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L) (hN : ∀ τ, IsUnit (N τ).det) :
    ∃ φ : ArcS Dw K →+* ArcS Dw L,
      (∀ g : LaurentSeries K, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g)) =
        algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) _ (MvPolynomial.C (LetterMap.coeffMap f g))) ∧
      ∀ τ, (letM Dw K τ).map φ = letM Dw L τ * (N τ).map ((arcι Dw L).comp (PowerSeries.C (R := L))) := by
  let g : MvPolynomial (ArcLt Dw) (LaurentSeries K) →+* ArcS Dw L :=
    MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp
      (MvPolynomial.C.comp (LetterMap.coeffMap f)))
      fun x => (letM Dw L x.1 * (N x.1).map ((arcι Dw L).comp (PowerSeries.C (R := L)))) x.2.1 x.2.2
  have hg : IsUnit (g (arcDet Dw K)) := by
    have e : g (arcDet Dw K) = (∏ τ, (letM Dw L τ).det) *
        ∏ τ, (arcι Dw L).comp (PowerSeries.C (R := L)) (N τ).det := by
      rw [← Finset.prod_mul_distrib]
      refine (map_prod g _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
      congr 1
      ext i k : 2
      exact MvPolynomial.eval₂Hom_X' _ _ _
    rw [e]
    exact (isUnit_prod_det Dw L).mul (IsUnit.prod_univ_iff.2 fun τ => (hN τ).map _)
  refine ⟨IsLocalization.Away.lift (arcDet Dw K) hg, fun p => ?_, fun τ => ?_⟩
  · rw [IsLocalization.Away.lift_eq]
    exact MvPolynomial.eval₂Hom_C _ _ _
  · ext i k : 2
    exact (IsLocalization.Away.lift_eq (arcDet Dw K) hg _).trans (MvPolynomial.eval₂Hom_X' _ _ _)

theorem arcι_C (Dw : Datum H) {L : Type} [Field L] (x : L) : arcι Dw L (PowerSeries.C (R := L) x) =
    algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x)) := by
  rw [← HahnSeries.ofPowerSeries_C]
  rfl

theorem isUnit_arcι_X (Dw : Datum H) (L : Type) [Field L] : IsUnit (arcι Dw L PowerSeries.X) := by
  have h : HahnSeries.ofPowerSeries ℤ L PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2 PowerSeries.X_ne_zero
  exact h.isUnit.map ((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp MvPolynomial.C)

theorem nontrivial_arcS (Dw : Datum H) (L : Type) [Field L] : Nontrivial (ArcS Dw L) :=
  (IsLocalization.injective (ArcS Dw L)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (LetterMap.det_ne_zero Dw L))).nontrivial

theorem exists_mul_pow (T : CDVR) {ϖ : T.V} (h : Irreducible ϖ) (y : T.Fr) :
    ∃ (v : T.V) (n : ℕ), y * algebraMap T.V T.Fr ϖ ^ n = algebraMap T.V T.Fr v := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors T.V) y
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero s.2) h
  exact ⟨a * u, n, by rw [← map_pow, ← hu, map_mul, ← mul_assoc, hs, map_mul]⟩

set_option maxHeartbeats 800000 in

theorem bcRigidAt_of_intModel : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (M : IntModel d Dv.Tv Dv.io Wl) (χw : Sp (PowerSeries Dv.Tv.V) ⟶ Yw.X) (Ww : Wit Yw M.aw χw) (y₀ : FrPt Xo c (ArcSR Dw Dv.Tv.V Dv.ϖ)) (ζ : K₁) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), d.OverBase → d.Normal ζ → χw ≫ Yw.s = spMap (PowerSeries.C (R := Dv.Tv.V)) ≫ spMap M.b → (∀ (x : c.F) (v : Dv.Tv.V) (n : ℕ), (Dv.io.comp (algebraMap c.F K₁)) x * algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ ^ n = algebraMap Dv.Tv.V Dv.Tv.Fr v → algebraMap c.F (ArcSR Dw Dv.Tv.V Dv.ϖ) x * arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ) ^ n = arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) v)) → IsArcFr Ww M.ew M.thw (arcιR Dw Dv.Tv.V Dv.ϖ) y₀ → FrChg (letMR Dw Dv.Tv.V Dv.ϖ) 1 y₀ Dv.yR → M.γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → (∀ τ, A τ * Bm τ = 1) → (∀ τ k l, M.g τ k l = lam τ k * A τ k l) → BcRigidAt Dv (Dv.io ζ * M.γ) lam Bm := by
  intro h1 h2 hU h5 E _ _ _ H Dw l Xo c K₁ _ _ _ d w Z Dv Wl Yw M χw Ww y₀ ζ lam A Bm hd hN hχ hpin hy₀ hyR _ hlam hAB hg
  have calcu := frChg_calculus E H Dw l Xo c
  have exu := frChg_exists_unique_units E H Dw l Xo c
  have frbc := GlobalTheory.FramedBaseChange.exists_frMap h1 E H Dw l Xo c
  have := nontrivial_arcS Dw Dv.Tv.Fr

  let N : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr :=
    fun τ => Matrix.of fun i k => Bm τ i k * (lam τ k)⁻¹
  have hNg : ∀ τ, N τ * M.g τ = 1 := fun τ => by
    rw [← mul_eq_one_comm.1 (hAB τ)]
    ext i k
    simp only [Matrix.mul_apply, N, Matrix.of_apply, hg]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, inv_mul_cancel_left₀ (hlam τ j)]
  let κ : Dv.Tv.Fr →+* ArcS Dw Dv.Tv.Fr := (arcι Dw Dv.Tv.Fr).comp (PowerSeries.C (R := Dv.Tv.Fr))

  obtain ⟨φ₀, hφC, hφX⟩ := exists_letterSub Dw Dv.io N fun τ => Matrix.isUnit_det_of_right_inverse (hNg τ)
  have hφι : φ₀.comp (arcι Dw K₁) = (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map Dv.io) := RingHom.ext fun p =>
    (hφC _).trans (by rw [LetterMap.coeffMap_ofPowerSeries]; rfl)
  have hφc : ∀ x : K₁, φ₀ (cst Dw x) = κ (Dv.io x) := fun x =>
    (RingHom.congr_fun hφι (PowerSeries.C x)).trans (congrArg (arcι Dw Dv.Tv.Fr) (PowerSeries.map_C _ _))
  let φ : ArcS Dw K₁ →ₐ[c.F] ArcS Dw Dv.Tv.Fr :=
    { φ₀ with commutes' := fun r => (congrArg φ₀ (arcS_pin Dw K₁ r)).trans ((hφc _).trans (Dv.algW_eq r).symm) }
  obtain ⟨-, -, -, ⟨ψ₀, hψι, hψX⟩, -⟩ := GlobalTheory.LetterDenom.main E H Dw Dv.Tv Dv.ϖ Dv.ϖ_irr.ne_zero
  have hψc : ∀ v, ψ₀ (arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C v)) = κ (algebraMap Dv.Tv.V Dv.Tv.Fr v) := fun v =>
    (RingHom.congr_fun hψι (PowerSeries.C v)).trans (congrArg (arcι Dw Dv.Tv.Fr) (PowerSeries.map_C _ _))
  have hψa : ∀ r : c.F, ψ₀ (algebraMap c.F _ r) = algebraMap c.F _ r := fun r => by
    obtain ⟨v, n, hv⟩ := exists_mul_pow Dv.Tv Dv.ϖ_irr (Dv.io (algebraMap c.F K₁ r))
    have e := congrArg ψ₀ (hpin r v n hv)
    rw [map_mul ψ₀, map_pow ψ₀, hψc, hψc, ← hv, map_mul κ, map_pow κ] at e
    have hu : IsUnit (κ (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) ^ n) :=
      (((map_ne_zero_iff _ (IsFractionRing.injective Dv.Tv.V Dv.Tv.Fr)).2 Dv.ϖ_irr.ne_zero).isUnit.map κ).pow n
    exact (hu.mul_right_cancel e).trans (Dv.algW_eq r).symm
  let ψ : ArcSR Dw Dv.Tv.V Dv.ϖ →ₐ[c.F] ArcS Dw Dv.Tv.Fr := { ψ₀ with commutes' := hψa }
  have hψM : ∀ τ, (letMR Dw Dv.Tv.V Dv.ϖ τ).map ψ = letM Dw Dv.Tv.Fr τ := fun τ =>
    Matrix.ext fun i k => hψX ⟨τ, i, k⟩

  obtain ⟨th₁, th₂, t₁, t₂, t₃⟩ := M.th_tie
  obtain ⟨e₁, e₂, l₁, l₂, -, l₃⟩ := M.e_tie
  have bcK : InBC Dv.io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK :=
    ⟨rfl, M.bcK.2⟩
  obtain ⟨w₁, -, -, -, n₁⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ Yw Dv.Tv.V Dv.Tv.Fr _ M.aw _
    (IsFractionRing.injective Dv.Tv.V Dv.Tv.Fr) _ M.bcw.1).2 (M.aK.restrict (c.V Wl).subtype) M.pw M.bcw
  obtain ⟨w₂, -, -, -, n₂⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ d.Y K₁ Dv.Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) _
    Dv.io.injective _ bcK.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK bcK
  obtain ⟨W₁, hW₁⟩ := w₁ χw Ww
  obtain ⟨W₂, hW₂⟩ := w₂ d.χ d.W
  have nz : ThNZ d.th := by
    obtain ⟨_, _, _, _, h, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h
  have hj : Mono Yw.j := GlobalTheory.ThetaShiftProofs.mono_j Yw (mono_spMap_subtype _)
  have hj' : Mono d.Y.j := GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)

  obtain ⟨y₁, hy₁⟩ := frbc _ _ ψ y₀
  have a₁ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Yw _ _ _ χw Ww _ _ M.thw_nz _ _ y₀ hy₀).2 hj _ ψ y₁ hy₁
  have a₂ : IsArcFr W₁ e₁ th₁ (arcι Dw Dv.Tv.Fr) y₁ :=
    GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ Yw _ _ M.aw χw Ww _ _ (M.aK.restrict (c.V Wl).subtype) _ M.pw W₁ hj M.bcw hW₁ _ _ _ _ l₁ t₁ _ _ y₁ (hψι ▸ a₁)
  obtain ⟨y₂, hy₂⟩ := (exu _ (fun τ => (M.g τ).map κ) (κ M.γ) y₁).1
    (fun τ => by
      have := (Matrix.isUnit_det_of_left_inverse (hNg τ)).map κ
      rwa [RingHom.map_det] at this) ((Ne.isUnit ‹M.γ ≠ 0›).map κ)
  have a₃ : IsArcFr W₁ e₂ th₂ (arcι Dw Dv.Tv.Fr) y₂ :=
    GlobalTheory.ArcQ.isArcFr_of_frChg_const h1 h2 E H Dw l Xo c _ _ Yw _ _ _ _ W₁ e₁ e₂ th₁ th₂ M.g M.γ (n₁ _ _ t₁ M.thw_nz) l₃ t₃ _ _ y₁ y₂ hj a₂ hy₂

  obtain ⟨x₀, hx₀, hxF⟩ := hN
  obtain ⟨x₁, hx₁⟩ := frbc _ _ φ x₀
  have b₁ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ d.Y _ _ _ d.χ d.W _ _ nz _ _ x₀ hx₀).2 hj' _ φ x₁ hx₁
  have b₂ : IsArcFr W₂ e₂ th₂ (arcι Dw Dv.Tv.Fr) x₁ :=
    GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ d.Y _ _ (d.a.restrict (c.V d.Wp).subtype) d.χ d.W _ _
      (M.aK.restrict (c.V d.Wp).subtype) _ M.pK W₂ hj' bcK hW₂ _ _ _ _ l₂ t₂ _ _ x₁ (hφι ▸ b₁)

  have hC : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R'),
      spMap (PowerSeries.map f) ≫ spMap (PowerSeries.C (R := R)) = spMap (PowerSeries.C (R := R')) ≫ spMap f :=
    fun f => by
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C _ _)
  obtain rfl : y₂ = x₁ := GlobalTheory.T.arc_framed_point_eq_of_models_over_base h1 h2 h5 E H Dw l Xo c _ _ M.aK _ _ Yw d.Y _ _ W₁ W₂
    (by rw [Category.assoc, hχ, ← Category.assoc, hC, Category.assoc, ← spMap_comp, ← M.bcw.1])
    (by rw [Category.assoc, hd, ← Category.assoc, hC, Category.assoc, ← spMap_comp, RingHom.comp_assoc])
    e₂ th₂ (n₂ _ _ t₂ nz) _ _ y₂ x₁ (isUnit_arcι_X Dw _) a₃ b₂

  obtain ⟨z₁, hz₁⟩ := frbc _ _ φ d.yF
  obtain ⟨z₂, hz₂⟩ := frbc _ _ ψ Dv.yR
  have c₁ := ((calcu _).1 _ _ _ _ _ _ _ hy₂).1 (((calcu _).2.2.1 _ φ _ _ _ _ _ _ hxF hx₁).1 hz₁)
  have c₂ := ((calcu _).2.2.1 _ ψ _ _ _ _ _ _ hyR hy₁).1 hz₂
  have eM : (fun τ => (letM Dw K₁ τ).map φ * (M.g τ).map κ) = fun τ => 1 * (letMR Dw Dv.Tv.V Dv.ϖ τ).map ψ :=
    funext fun τ => by
      rw [hψM, one_mul]
      refine (congrArg (· * (M.g τ).map κ) (hφX τ)).trans ?_
      change letM Dw Dv.Tv.Fr τ * (N τ).map κ * (M.g τ).map κ = _
      rw [mul_assoc, ← Matrix.map_mul, hNg, Matrix.map_one _ (map_zero κ) (map_one κ), mul_one]
  have eS : φ (cst Dw ζ) * κ M.γ = κ (Dv.io ζ * M.γ) * ψ 1 := by
    rw [map_one, mul_one, map_mul]
    exact congrArg (· * κ M.γ) (hφc ζ)
  rw [eM, eS] at c₁
  have c₃ := ((calcu _).1 _ (fun _ => 1) _ _ _ _ _ c₂).2 c₁
  have hu := ((exu _ _ _ _).2.2.1 _ c₃).2
  refine ⟨φ, ψ, z₁, z₂, fun o => o.elim hu.unit fun _ => 1, fun f => ⟨_, fun _ => rfl, hφC f⟩, fun x => ?_,
    fun p => RingHom.congr_fun hψι p, hψX, arcι_C Dw _, fun _ => rfl, hz₁, hz₂,
    ((calcu _).2.2.2 _ _ _).2 ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i,
      fun τ i j h => Matrix.one_apply_ne h.ne, c₃⟩⟩
  refine (congrFun (congrFun (hφX x.1) x.2.1) x.2.2).trans ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (arcι_C Dw _)

end GlobalTheory.ArcRigidity
