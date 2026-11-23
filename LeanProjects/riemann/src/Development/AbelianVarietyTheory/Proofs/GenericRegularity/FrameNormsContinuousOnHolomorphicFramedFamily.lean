import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermEqOfNormalised
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVectorStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriodStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamilyStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSectionStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrtStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm.Hol

theorem continuousOn_form {V : Type} [TopologicalSpace V] {g : ℕ} {B : Set V} (h τ : V → Matrix (Fin g) (Fin g) ℂ)
    (hh : ∀ i j, ContinuousOn (fun b => h b i j) B) (hτ : ∀ i j, ContinuousOn (fun b => τ b i j) B)
    (hp : ∀ b ∈ B, ((τ b).map Complex.im).PosDef) :
    ContinuousOn (fun b => ((τ b).map Complex.im).det) B ∧ ∀ i j, ContinuousOn (fun b =>
      ((h b)ᵀ * (((τ b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * (h b).map (starRingEnd ℂ)) i j) B := by
  simp only [continuousOn_iff_continuous_restrict] at hh hτ ⊢
  have h1 : Continuous fun b : B => h b := continuous_matrix hh
  have h2 : Continuous fun b : B => (τ b).map Complex.im :=
    (continuous_matrix hτ : Continuous fun b : B => τ b).matrix_map Complex.continuous_im
  have h3 : Continuous fun b : B => ((τ b).map Complex.im)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (h2.matrix_det.inv₀ fun b => (hp b b.2).det_pos.ne').smul h2.matrix_adjugate
  refine ⟨h2.matrix_det, fun i j => ?_⟩
  exact ((h1.matrix_transpose.matrix_mul (h3.matrix_map Complex.continuous_ofReal)).matrix_mul
    (h1.matrix_map Complex.continuous_conj)).matrix_elem i j

theorem exists_continuous_form_mean {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (hty : IsTypeFn H Dw.p Dw.q ty) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (hB : IsOpen B)
    (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) (hy : ∀ b ∈ B, FrMap (φ b) yA (y b))
    (hP : IsHolPeriods (F.Di k) ty B P) (hx : ∀ b ∈ B, (y b).x = F.u k (P b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B' : Set (Fin m → ℂ)) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (μ : (Fin m → ℂ) → ℝ),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ i j, ContinuousOn (fun b => Hm b i j) B') ∧ ContinuousOn μ B' ∧
      ∀ b ∈ B', (∀ v w, (hermForm (Hm b) (P b v) (P b w)).im = (F.Di k).EF v w) ∧
        AHMean F k (P b) (y b).x (y b).s (μ b) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨bas, hbas, -⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (F.Di k) g ty bas hbas
  have hP' : IsHolPeriods (F.Di k) ty (Metric.ball b₀ ε) P :=
    ⟨fun b hb => hP.1 b (hsub hb), fun v => (hP.2 v).mono hsub⟩
  choose! h τ hn hdet hsym hpos _ using fun b hb => hR1 _ (hP'.1 b hb)
  have hhol := hR2 m _ P h τ hP' hn
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := F.theta k m _ P bas (-1) h τ Metric.isOpen_ball
    (convex_ball b₀ ε).isPreconnected hP' (fun a b => by rw [hbas]; simp) (fun b hb => ⟨hpos b hb, hn b hb⟩)
  obtain ⟨t1, t2⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ hc₁ hc₂
  have t3 := t2 m _ h τ Metric.isOpen_ball (fun b hb => ⟨hsym b hb, hpos b hb⟩) hhol
  obtain ⟨fr, κ, hfr, hκ, hval⟩ := GlobalTheory.T.exists_holomorphicFactor_generator_thetaSection E H Dw l Xo c σ σ' g ty F k A yA m _ φ y P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) Metric.isOpen_ball
    (fun a => (hφ a).mono hsub) (fun b hb => hy b (hsub hb)) hP' (fun b hb => hx b (hsub hb))
    (fun z => DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, z) : (Fin m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2))
      t3 (by fun_prop) fun b hb => ⟨hb, trivial⟩)
    (fun b hb => by
      obtain ⟨-, w, hw⟩ := t1 _ (hsym b hb) (hpos b hb)
      obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet b hb)) w
      exact ⟨z, by rw [hz]; exact hw⟩) hθ
  obtain ⟨c1, c2⟩ := continuousOn_form h τ (fun i j => (hhol i j).1.continuousOn)
    (fun i j => (hhol i j).2.continuousOn) hpos
  refine ⟨Metric.ball b₀ ε, _, fun b => ‖κ b‖ ^ 2 * (Real.sqrt (2 ^ g * ((τ b).map Complex.im).det))⁻¹,
    Metric.isOpen_ball, Metric.mem_ball_self hε, hsub, c2, ?_, fun b hb => ⟨?_, ?_⟩⟩
  · refine (hκ.continuousOn.norm.pow 2).mul (ContinuousOn.inv₀ (continuousOn_const.mul c1).sqrt fun b hb => ?_)
    have := (hpos b hb).det_pos
    positivity
  · obtain ⟨Hm, -, -, hH⟩ := (hP'.1 b hb).2.2.2.2
    rw [← (GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ (h b) (τ b) Hm hbas (hP'.1 b hb) (hn b hb)
      ⟨hsym b hb, hpos b hb⟩ hH).1]
    exact hH
  · exact GlobalTheory.T.meanSquare_multiple_thetaSection_family E H Dw l Xo σ' g ty F k m _ P fr bas b (h b) (τ b) c₁ c₂ _ _ (κ b) hb (hP'.1 b hb) hbas (hdet b hb)
      (hsym b hb) (hpos b hb) (hn b hb) hc₁ hc₂ hfr (hx b (hsub hb)) (hval b hb).1 (hval b hb).2

end GlobalTheory.FrameNorm.Hol

theorem GlobalTheory.FrameNorm.fn_continuousOn_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn _ hpin σ hσ A _ _ yA m B φ y hB hφ hy i b₀ hb₀
  obtain ⟨hr, hty, hcov, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU σ hσ
  obtain ⟨B₁, k, P, hB₁, hb₁, hs₁, hP, hyP⟩ := GlobalTheory.T.exists_holomorphic_periods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k₀, x₁, t₁, ht₁⟩ := hcov (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k₀ x₁
  obtain rfl : ik k₀ = k := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨d, hd, horth⟩ := GlobalTheory.T.period_eq_triangular_orthonormal_alt E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k₀).1 (hty k₀).2 (hef k₀)
    (GlobalTheory.T.im_neg_of_frame_period_vector E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ hr (hty k₀).1 (hty k₀).2 (hef k₀) x₁.1 x₁.2 P₁ hP₁ hP₁')
  obtain ⟨B₂, Hm, μ, hB₂, hb₂, hs₂, hHm, hμ, hAH⟩ := GlobalTheory.FrameNorm.Hol.exists_continuous_form_mean F (ik k₀)
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e) yA φ y P hB₁ (fun a => (hφ a).mono hs₁)
    (fun b hb => hy b (hs₁ hb)) hP (fun b hb => (hyP b hb).1) hb₁
  have key : ∀ b ∈ B₂, ∃ S : Matrix (Fin g) (Fin g) ℂ, (IsUnit S.det ∧
      (∀ j j', S j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      Hm b = Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))) ∧
      (∀ j, |fn σ (y b) (some (e j))| = ‖S j j‖ * Real.sqrt (2 * Real.pi * xR)) ∧
      |fn σ (y b) none| = Real.sqrt (μ b) := by
    intro b hb
    have hp := hP.1 b (hs₂ hb)
    obtain ⟨x₀, hx₀, hunit, S, hS, hsupp, hper, hform⟩ := horth _ hp
    obtain ⟨P₀, hP₀, hP₀', hux, hud, hmean⟩ := hun k₀ ⟨x₀, hx₀⟩
    have hPS : ∀ a, P₀ a = S *ᵥ P b a := fun a => funext fun j => (hP₀ a j).trans (hper a j).symm
    obtain ⟨t, ht, htS⟩ := GlobalTheory.T.triangular_frame_change_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ S (y b) ((U σ).un k₀ ⟨x₀, hx₀⟩) hp hP₀' hPS hsupp
      (hyP b (hs₂ hb)).1 hux (hyP b (hs₂ hb)).2 hud
    have hfn := hpin.1 σ hσ k₀ ⟨x₀, hx₀⟩ hunit t (y b) ht
    refine ⟨S, ⟨hS, hsupp, ?_⟩, fun j => ?_, ?_⟩
    · refine GlobalTheory.UnitDet.eq_of_im_hermForm_eq _ hp.2.2.2.1 _ _ ?_
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← GlobalTheory.UnitDet.hermForm_mulVec, hform, (hAH b hb).1]
    · rw [hfn, ← htS j]
      rfl
    · obtain ⟨hxx, -, pm, p1, p2, p3⟩ := ht
      have hbc : SecBC (RingHom.id ℂ) (toC (t none : CAt σ)) ((U σ).un k₀ ⟨x₀, hx₀⟩).x (y b).x
          ((U σ).un k₀ ⟨x₀, hx₀⟩).s (y b).s := ⟨pm, p1, p2.trans (by rw [GlobalTheory.Frames.SecCalc.spMap_id']; exact (Category.comp_id _).symm), p3⟩
      have h1 := GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections E H Dw l Xo _ g _ F _ P₀ (P b) S _ _ _ _ _ 1 (μ b) hP₀' hp hPS hux hxx hbc (hmean hunit)
        (hAH b hb).2
      rw [hfn, h1, mul_one, Real.sqrt_sq (norm_nonneg _)]
      exact mul_one _
  choose! S hS hlie hgen using key
  refine ContinuousAt.continuousWithinAt (ContinuousOn.continuousAt (s := B₂) ?_ (hB₂.mem_nhds hb₂))
  cases i with
  | none => exact hμ.sqrt.congr hgen
  | some s =>
    obtain ⟨j, rfl⟩ := e.surjective s
    refine ((GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor g (E →+* ℂ) _ (fun j => (e j).1) (fun j => (e j).2) d B₂ S Hm (fun j j' h1 h2 => ?_) hd hHm hS
      j).mul continuousOn_const).congr fun b hb => hlie b hb j
    exact e.injective (Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2))
