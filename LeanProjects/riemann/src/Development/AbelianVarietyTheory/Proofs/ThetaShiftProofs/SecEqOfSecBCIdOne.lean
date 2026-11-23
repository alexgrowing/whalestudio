import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArcPtX
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfEqMulInvPow
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open MonoidalCategory CartesianMonoidalCategory

namespace GlobalTheory.ArcDatumExists

theorem isUnit_det_letM {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (K : Type) [Field K] (τ : E →+* ℂ) : IsUnit (letM Dw K τ).det := by
  have h1 : IsUnit (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K) (arcDet Dw K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 : Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K))) ∣ arcDet Dw K :=
    Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K)))) (Finset.mem_univ τ)
  have h3 := isUnit_of_dvd_unit
    (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) h2) h1
  rw [RingHom.map_det] at h3
  exact h3

theorem flat_of_field {K S : Type} [Field K] [CommRing S] (f : K →+* S) : f.Flat := by
  let _ := f.toAlgebra
  exact (inferInstance : Module.Flat K S)

theorem appLE_id_apply {X : Scheme.{0}} (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom r = r := by
  have : Scheme.Hom.appLE (𝟙 X) U U h = 𝟙 _ := by
    unfold Scheme.Hom.appLE
    rw [Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]; rfl

theorem sec_eq_of_secBC_id_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (h : SecBC (RingHom.id S) 1 x x s s') (i : (PPx x).ι) : s'.f i = s.f i := by
  obtain ⟨pm, h1, h2, h3⟩ := h
  have hid : spMap (RingHom.id S) = 𝟙 _ := by
    unfold spMap; simp
  have hpm : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [hid] at h2
      simpa using h2
    · simpa using h1
  subst hpm
  have h4 := h3 i le_rfl
  have hs : scal x (1 : S) i = 1 := by
    unfold scal Out.liftFun
    simp
  rw [hs, one_mul] at h4
  rw [← h4]
  exact appLE_id_apply _ _ _

theorem isArcPt3At_of_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    {W : Wit Y a χ} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {th : a.D₀.P.L.Sec}
    [Algebra c.F (ArcS Dw K₁)] {y₀ yF : FrPt Xo c (ArcS Dw K₁)} (hth : ∃ j, th.f j ≠ 0)
    (hfr : IsArcFr W e th (arcι Dw K₁) y₀) (hchg : FrChg (letM Dw K₁) 1 y₀ yF) : IsArcPt3At Y a χ W yF th := by
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := yF
  obtain ⟨hx, hu, hs⟩ := hchg
  dsimp only at hx hu hs
  subst hx
  obtain ⟨z, t', m1, m2, φ, -, -, -, h0, hm, -, θ, w1, w2, σ', s1, θ2, hθ, r1, r2, i1, i2, ps, hg⟩ := hfr
  obtain ⟨σ, fam, θ', a1, a2, a3, a4⟩ := hθ
  refine ⟨σ, fam, θ', θ, hth, a1, a2, a3, a4, t', m1, m2, w1, w2, σ', s1, θ2, ⟨φ, h0, hm⟩, r1, r2, i1, i2, ps, ?_⟩
  intro g g1 g2 j h
  rw [hg g g1 g2 j h]
  exact congrArg _ (sec_eq_of_secBC_id_one _ _ _ hs _).symm

theorem exists_arcDatum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (Wp : ValuationSubring ℂ) (Y : Model Xo c (c.V Wp).subtype), Y.N4 → ∀ a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁), ∃ (χ : Sp (PowerSeries K₁) ⟶ Y.X) (W : Wit Y (a.restrict (c.V Wp).subtype) χ), (∃ e, ArcLieBasis W e) ∧ ∀ e, ArcLieBasis W e → ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∀ (μ : ArcLt Dw →₀ ℕ) (jj : ℤ), ∃ d : ArcDatum Xo c K₁, d.Wp = Wp ∧ HEq d.Y Y ∧ d.a = a ∧ HEq d.e e ∧ HEq d.th th ∧ d.μ = μ ∧ d.jj = jj ∧ d.OverBase ∧ d.Normal 1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ Wp Y hN4 a
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨χ, hχ, -⟩ := hN4 K₁ ((algebraMap c.F K₁).comp (c.V Wp).subtype) 1
    (a.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField K₁, rfl⟩)
  obtain ⟨hs, -, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ χ).1 hW
  refine ⟨χ, W, ?_, fun e he th hth μ jj => ?_⟩
  · obtain ⟨e, -, he⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ))
      ((algebraMap K₁ (FractionRing K₁)).comp (algebraMap c.F K₁)) rfl (fun _ _ => rfl)
      (GlobalTheory.JointModelGuards.exists_root_and_zeta l c Wp)
    exact ⟨e, he⟩
  · have hcomp : (algebraMap c.F (ArcS Dw K₁)).comp (c.V Wp).subtype =
        (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp ((algebraMap c.F K₁).comp (c.V Wp).subtype)) := by
      ext r
      simp only [RingHom.comp_apply]
      exact arcS_pin Dw K₁ ((c.V Wp).subtype r)
    obtain ⟨z, hz1, hz2⟩ := arcPt_point (Dw := Dw) Y ((algebraMap c.F K₁).comp (c.V Wp).subtype)
      hcomp χ hs (fun x hx => hj x (by rwa [map_one, one_mul]))
    have hnz : ThNZ th := (GlobalTheory.ThetaOverField.nonzero_generates hL hL2 K₁ a.D₀ th).1.1 hth
    have hflat : ((arcι Dw K₁).comp (PowerSeries.C (R := K₁))).Flat := flat_of_field _
    have hz3 : z ≫ pullback.fst _ _ ≫ Xo.s = sOf c (ArcS Dw K₁) := by
      rw [Y.jQ_over] at hz2
      rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]
      rfl
    obtain ⟨y₀, -, hy₀⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ)) e th he hnz (Or.inl (Field.toIsField K₁))
      (ArcS Dw K₁) (arcι Dw K₁) z hflat hz1 hz3 (fun τ x => arcS_pin Dw K₁ (embK c τ x))
    obtain ⟨yF, hyF⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (ArcS Dw K₁) (letM Dw K₁) 1 y₀).1
      (isUnit_det_letM Dw K₁) isUnit_one
    have h12 := hy₀.isFramedPoint_changed_by_letters hyF hs
    have h3 := isArcPt3At_of_frChg (W := W) (e := e) hth hy₀ hyF
    refine ⟨⟨Wp, Y, a, χ, W, e, yF, th, h12, h3, μ, jj⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, hs,
      y₀, hy₀, ?_⟩
    have h1 : GlobalTheory.ArcQ.cst Dw (1 : K₁) = 1 := by simp only [GlobalTheory.ArcQ.cst, map_one]
    rw [h1]
    exact hyF

end GlobalTheory.ArcDatumExists
