import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightRightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPshPhMu
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.PrimeSpectrumDualEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormIteratedFDerivApplyLeOfHomogeneousPart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.SheetPot

open GlobalTheory.CompanionTheory.Ar.HodgeAdj

theorem eig_of_isDiff {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ G.left} {L : LB A.left} {g : ℕ} (hpb : IsGrpPullback A G z φ) (u : HolUnif A L g)
    (f₀ : G ⟶ G) [IsMonHom f₀] (B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hB : ∀ p, (u.ex (B p)).left ≫ φ = (u.ex p).left ≫ φ ≫ f₀.left)
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) {c : ℂ} (hsc : v ≫ f₀ = LieTangent.epsScale z c ≫ v)
    {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) {x : Fin g → ℂ} (hd : u.IsDiff x v') :
    B x = c • x := by
  obtain ⟨f, hfm, hf⟩ := exists_endo hpb f₀
  have hF : ∀ p, u.ex (B p) = u.ex p ≫ f := fun p =>
    Over.OverMorphism.ext (hpb.1.hom_ext (by
      rw [hB, Over.comp_left, Category.assoc, hf]) (by rw [Over.w, Over.w]))
  have t₁ : IsTangent v' := by
    rw [lft_unique hpb e]
    exact isTangent_lft hpb hv
  have d1 := GlobalTheory.HomLinear.isDiff_comp u u f B hF t₁ hd
  have d2 := GlobalTheory.CMCurveTest.isDiff_scaleVec u hd c
  have e1 : (v' ≫ f).left ≫ φ = (v ≫ f₀).left := by
    rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, e, Over.comp_left]
  have e2 : (GlobalTheory.CMCurveTest.scaleVec c v').left ≫ φ = (v ≫ f₀).left := by
    rw [hsc]
    have hm : GlobalTheory.CompanionTheory.Ar.epsMul c = epsScaleR c := by
      refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
      · simp [epsScaleR]
      · simp [epsScaleR]
    show (spMap (epsScaleR c) ≫ v'.left) ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul c)) ≫ v.left
    rw [Category.assoc, e, hm]
  have t₂ : IsTangent (v' ≫ f) := by
    rw [lft_unique hpb e1]
    exact isTangent_lft hpb (isTanAt_comp f₀ hv)
  have key : GlobalTheory.CMCurveTest.scaleVec c v' = v' ≫ f := (lft_unique hpb e2).trans (lft_unique hpb e1).symm
  rw [key] at d2
  exact eq_of_isDiff u t₂ d1 d2

section LinAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def coordMat {m : ℕ} (L : Matrix (Fin m) (Fin g) ℂ) (u : Fin m → Fin g → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of u * Lᵀ

theorem gram_eq (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = (Matrix.of u).map (starRingEnd ℂ) * R.Hmᵀ * (Matrix.of u)ᵀ := by
  ext a b
  simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

theorem gram_det_re_of_span (R : RiemLat E g Λ) {m : ℕ} (x b : Fin m → Fin g → ℂ) (L : Matrix (Fin m) (Fin g) ℂ)
    (hx : ∀ a, x a ∈ Submodule.span ℂ (Set.range b)) (hb : (coordMat L b).det ≠ 0) :
    (R.gram x).det.re = ‖(coordMat L x).det / (coordMat L b).det‖ ^ 2 * (R.gram b).det.re := by
  have h : ∀ a, ∃ c : Fin m → ℂ, ∑ i, c i • b i = x a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hx a)
  choose T hT using h
  let T' : Matrix (Fin m) (Fin m) ℂ := Matrix.of T
  have hX : Matrix.of x = T' * Matrix.of b := by
    ext a k
    simp only [Matrix.of_apply, Matrix.mul_apply, T', ← hT a, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : coordMat L x = T' * coordMat L b := by
    simp only [coordMat, hX, Matrix.mul_assoc]
  have h2 : (coordMat L x).det / (coordMat L b).det = T'.det := by
    rw [h1, Matrix.det_mul, mul_div_assoc, div_self hb, _root_.mul_one]
  have h3 : R.gram x = T'.map (starRingEnd ℂ) * R.gram b * T'ᵀ := by
    rw [gram_eq, gram_eq, hX, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have h4 : (T'.map (starRingEnd ℂ)).det = starRingEnd ℂ T'.det := by
    have := (RingHom.map_det (starRingEnd ℂ) T').symm
    simpa [RingHom.mapMatrix_apply] using this
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h4, h2]
  have h5 : starRingEnd ℂ T'.det * (R.gram b).det * T'.det =
      ((‖T'.det‖ ^ 2 : ℝ) : ℂ) * (R.gram b).det := by
    have : starRingEnd ℂ T'.det * T'.det = ((‖T'.det‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← this]
    ring
  rw [h5, Complex.re_ofReal_mul]

theorem exists_coordMat_one {m : ℕ} (b : Fin m → Fin g → ℂ) (hb : LinearIndependent ℂ b) :
    ∃ L : Matrix (Fin m) (Fin g) ℂ, coordMat L b = 1 := by
  have hinj : Function.Injective (Matrix.of b)ᵀ.mulVec := Matrix.mulVec_injective_iff.2 hb
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective ((Matrix.of b)ᵀ.mulVecLin)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have e : LinearMap.toMatrix' f * (Matrix.of b)ᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hf
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  have := congrArg Matrix.transpose e
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem analyticAt_det_coordMat {n m : ℕ} {u : Fin m → (Fin n → ℂ) → Fin g → ℂ} {t : Fin n → ℂ}
    (L : Matrix (Fin m) (Fin g) ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) t) :
    AnalyticAt ℂ (fun t' => (coordMat L fun i => u i t').det) t := by
  have hc : ∀ (i : Fin m) (k : Fin g), AnalyticAt ℂ (fun t' => u i t' k) t := fun i k =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) k).analyticAt _).comp (hu i)
  simp only [Matrix.det_apply, coordMat, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ?_)
  exact Finset.analyticAt_fun_sum _ fun k _ => (hc _ k).mul analyticAt_const

theorem exists_log_norm_analytic {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀)
    (h0 : F t₀ ≠ 0) : ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, Real.log ‖F t‖ = (G t).re := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have h1 : ∀ᶠ t in 𝓝 t₀, F t / F t₀ ∈ Complex.slitPlane := by
    have : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
    exact hH.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds this)
  refine ⟨fun t => Complex.log (F t / F t₀) + (Real.log ‖F t₀‖ : ℂ),
    (hH.clog (by simpa [div_self h0] using Complex.one_mem_slitPlane)).add analyticAt_const, ?_⟩
  filter_upwards [h1] with t ht
  have hne : F t / F t₀ ≠ 0 := Complex.slitPlane_ne_zero ht
  have hFt : F t ≠ 0 := fun h => hne (by simp [h])
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 hFt) (norm_ne_zero_iff.2 h0)]
  ring

end LinAlg

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem pot_of_family (F : UnivFam E Ψ j j' n g Λ) {V : Set (Fin n → ℂ)} (hV : IsOpen V) (hVb : V ⊆ ballDom F.q)
    {t : Fin n → ℂ} (ht : t ∈ V) (x : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ)
    (hx : ∀ τ i, AnalyticAt ℂ (x τ i) t)
    (hev : ∀ᶠ t' in 𝓝 t, ∀ τ i, x τ i t' ∈ eigSp (F.R t').B (F.σ τ))
    (hpos : ∀ τ, 0 < ((F.R t).gram fun i => x τ i t).det.re) :
    ∃ Q : (Fin n → ℂ) → ℂ, AnalyticAt ℂ Q t ∧ Q t ≠ 0 ∧ ∀ᶠ t' in 𝓝 t,
      (∀ τ, 0 < ((F.R t').gram fun i => x τ i t').det.re) ∧
      ∑ τ, Real.log ((F.R t').gram fun i => x τ i t').det.re = ballPot F.q t' + 2 * Real.log ‖Q t'‖ := by
  classical
  have hfr := F.frames
  have hbt : ∀ t' ∈ V, ∀ τ, LinearIndependent ℂ (fun i => F.b τ i t') := fun t' h τ => (hfr.2 t' (hVb h) τ).1
  choose L hL using fun τ => exists_coordMat_one (fun i => F.b τ i t) (hbt t ht τ)
  have hba : ∀ τ i, AnalyticAt ℂ (F.b τ i) t := fun τ i =>
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hV ((hfr.1 τ i).mono hVb)) t ht
  let db : Ψ → (Fin n → ℂ) → ℂ := fun τ t' => (coordMat (L τ) fun i => F.b τ i t').det
  let dx : Ψ → (Fin n → ℂ) → ℂ := fun τ t' => (coordMat (L τ) fun i => x τ i t').det
  have hdb : ∀ τ, AnalyticAt ℂ (db τ) t := fun τ => analyticAt_det_coordMat (L τ) (hba τ)
  have hdx : ∀ τ, AnalyticAt ℂ (dx τ) t := fun τ => analyticAt_det_coordMat (L τ) (hx τ)
  have hdb1 : ∀ τ, db τ t ≠ 0 := fun τ => by
    show (coordMat (L τ) fun i => F.b τ i t).det ≠ 0
    rw [hL τ, Matrix.det_one]
    exact one_ne_zero
  let q : Ψ → (Fin n → ℂ) → ℂ := fun τ t' => dx τ t' / db τ t'
  have hqa : ∀ τ, AnalyticAt ℂ (q τ) t := fun τ => (hdx τ).div (hdb τ) (hdb1 τ)
  have hev2 : ∀ᶠ t' in 𝓝 t, ∀ τ, db τ t' ≠ 0 :=
    Filter.eventually_all.2 fun τ => (hdb τ).continuousAt.eventually_ne (hdb1 τ)
  have hgram : ∀ t' ∈ V, (∀ τ i, x τ i t' ∈ eigSp (F.R t').B (F.σ τ)) → (∀ τ, db τ t' ≠ 0) → ∀ τ,
      ((F.R t').gram fun i => x τ i t').det.re =
        ‖q τ t'‖ ^ 2 * ((F.R t').gram fun i => F.b τ i t').det.re := fun t' h1 h2 h3 τ =>
    gram_det_re_of_span _ _ _ (L τ) (fun i => by
      rw [(hfr.2 t' (hVb h1) τ).2]
      exact h2 τ i) (h3 τ)
  have hbpos : ∀ t' ∈ V, ∀ τ, 0 < ((F.R t').gram fun i => F.b τ i t').det.re := fun t' h τ =>
    GlobalTheory.CompanionTheory.Ar.Cusp.MuPsh.gram_det_pos (F.R t') _ (hbt t' h τ)
  have hq0 : ∀ τ, q τ t ≠ 0 := fun τ h0 => by
    have h := hgram t ht hev.self_of_nhds hev2.self_of_nhds τ
    rw [h0] at h
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h
    exact (hpos τ).ne' h
  refine ⟨fun t' => ∏ τ, q τ t', Finset.analyticAt_fun_prod _ fun τ _ => hqa τ,
    Finset.prod_ne_zero_iff.2 fun τ _ => hq0 τ, ?_⟩
  have hev3 : ∀ᶠ t' in 𝓝 t, ∀ τ, q τ t' ≠ 0 :=
    Filter.eventually_all.2 fun τ => (hqa τ).continuousAt.eventually_ne (hq0 τ)
  filter_upwards [hV.mem_nhds ht, hev, hev2, hev3] with t' h1 h2 h3 h4
  refine ⟨fun τ => ?_, ?_⟩
  · rw [hgram t' h1 h2 h3 τ]
    exact mul_pos (pow_pos (norm_pos_iff.2 (h4 τ)) 2) (hbpos t' h1 τ)
  have e1 : ballPot F.q t' = ∑ τ, Real.log ((F.R t').gram fun i => F.b τ i t').det.re := by
    rw [← F.logDet_eq t' (hVb h1)]
    rfl
  rw [e1, norm_prod, Real.log_prod (fun τ _ => norm_ne_zero_iff.2 (h4 τ)), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hgram t' h1 h2 h3 τ, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (h4 τ))) (hbpos t' h1 τ).ne',
    Real.log_pow]
  push_cast
  ring

end Family

end GlobalTheory.CompanionTheory.Ar.Cusp.SheetPot

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open GlobalTheory.CompanionTheory.Ar.Cusp.SheetPot

theorem phMu_eq_ballPot_half : GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E (CMType H) Dc.j Dc.j' Dc.n g Λ) (V : Set (Fin Dc.n → ℂ)) (z : (Fin Dc.n → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (gm : (Fin Dc.n → ℂ) → (Σ k, J k) → ℂ), IsOpen V → V ⊆ ballDom F.q → DifferentiableOn ℂ gm V → (∀ t ∈ V, CoordsAt Or.𝔐.ξ Dc.y (z t) (gm t) ∧ Or.𝔐.Interior (z t) ∧ Or.𝔐.LabVal (z t) Or.sm F.σ) → (∀ t₀ ∈ V, ∀ (m : ℕ) (s : Fin m → Or.𝔐.Li), (∀ a, ∃ v, Or.𝔐.M.ValAt (z t₀) (s a) v) → ∃ x : Fin m → (Fin Dc.n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ Or.𝔐.t.G), (∀ a, Or.𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec Or.𝔐.t (z t) (F.R t) (fun a => x a t) v) → ∀ t ∈ V, ∃ G : (Fin Dc.n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, phMu Hd (gm t') = ballPot F.q t' / 2 + (G t').re := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or g Λ _ _ F V z gm hV hVb hgm hpt hlat t ht
  classical
  obtain ⟨hco, hin, -⟩ := hpt t ht
  obtain ⟨⟨d⟩, hall⟩ := (GlobalTheory.T.intersection_system_weight_right hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or (z t) (gm t) hco)
  obtain ⟨⟨s, hs⟩, hP⟩ := hall d
  obtain ⟨-, hv0, -⟩ := hP s hs

  let e := Fintype.equivFin (CMType H × Fin (Dc.N - Dc.j))
  let sF : Fin (Fintype.card (CMType H × Fin (Dc.N - Dc.j))) → Or.𝔐.Li := fun a => s (e.symm a).1 (e.symm a).2
  have hsF : ∀ τ p, sF (e (τ, p)) = s τ p := fun τ p => by simp [sF]
  obtain ⟨Γ₀, hΓ₀, hp₀, -⟩ := PhMuFree.norm_eq Or hco hin d hs
  have hval : ∀ a, ∃ v, Or.𝔐.M.ValAt (z t) (sF a) v := fun a => by
    obtain ⟨v, hv, -⟩ := hΓ₀ (e.symm a).1
    exact ⟨_, hv _⟩
  obtain ⟨xF, hxa, hxe⟩ := hlat t ht _ sF hval
  let x : CMType H → Fin (Dc.N - Dc.j) → (Fin Dc.n → ℂ) → Fin g → ℂ := fun τ i => xF (e (τ, i))
  let Γ' : (Fin Dc.n → ℂ) → CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ := fun t' τ =>
    Matrix.of fun p q => (Real.pi : ℂ) * (F.R t').ip (x τ p t') (x τ q t')

  have hfib : ∀ t' ∈ V, ∀ v : Fin _ → (epsAt (z t') ⟶ Or.𝔐.t.G), (∀ a, Or.𝔐.M.ValAt (z t') (sF a) (v a)) →
      FibreLatVec Or.𝔐.t (z t') (F.R t') (fun a => xF a t') v →
      (∀ τ i, x τ i t' ∈ eigSp (F.R t').B (F.σ τ)) ∧
        ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L (z t') (s τ) (Γ' t' τ) := by
    intro t' ht' v hv hf
    have hv' : ∀ τ p, Or.𝔐.M.ValAt (z t') (s τ p) (v (e (τ, p))) := fun τ p => hsF τ p ▸ hv _
    refine ⟨fun τ i => ?_, fun τ => ⟨fun p => v (e (τ, p)), fun p => hv' τ p, fun p q =>
      MuPsh.hodgeInnerProduct_of_fibreLatticeVector hf (fun a => (hv a).isTanAt) (e (τ, p)) (e (τ, q))⟩⟩
    refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, -, -, h3⟩ := hf
    obtain ⟨v₁, e₁, d₁⟩ := h3 (e (τ, i))
    obtain ⟨h1, w, hw, hr⟩ := (hpt t' ht').2.2 τ a
    haveI := Or.𝔐.t.act.hom a
    have hsc := PhMuFree.val_eig Or.𝔐 Or.𝔐.tie.gen h1 (Or.sm τ) a w hw (hs τ i).1 (hv' τ i)
    exact eig_of_isDiff hpb u (Or.𝔐.t.act.act a) ((F.R t').B a) (fun p => hact a p) (hv' τ i).isTanAt
      (c := F.σ τ a) (by rw [← hr]; exact hsc) e₁ d₁
  have hΓdet : ∀ t' τ, (Γ' t' τ).det.re =
      Real.pi ^ (Dc.N - Dc.j) * ((F.R t').gram fun i => x τ i t').det.re := fun t' τ => by
    have e1 : Γ' t' τ = (Real.pi : ℂ) • (F.R t').gram fun i => x τ i t' := by
      ext p q; rfl
    rw [e1, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

  have hpos : ∀ τ, 0 < ((F.R t).gram fun i => x τ i t).det.re := fun τ => by
    obtain ⟨v, hv, hf⟩ := hxe.self_of_nhds
    have hg := (hfib t ht v hv hf).2 τ
    haveI : CharZero Ω := algebraRat.charZero Ω
    have hpol := GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 (z t) hin
    have e1 := HodgeMetric.gramAt_unique_of_polarisedAt E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 (z t) _ (s τ) _ _ hpol
      hg (hΓ₀ τ)
    have h2 := PhMuFree.det_re_pos (hp₀ τ)
    rw [← e1, hΓdet] at h2
    exact (pos_iff_pos_of_mul_pos h2).1 (pow_pos Real.pi_pos _)
  have hEig : ∀ᶠ t' in 𝓝 t, ∀ τ i, x τ i t' ∈ eigSp (F.R t').B (F.σ τ) := by
    filter_upwards [hxe, hV.mem_nhds ht] with t' ⟨v, hv, hf⟩ h1
    exact (hfib t' h1 v hv hf).1
  obtain ⟨Q, hQa, hQ0, hQe⟩ := pot_of_family F hV hVb ht x (fun τ i => hxa _) hEig hpos

  have hgma := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hV hgm t ht
  have hex : ∃ v, IsValueAt Dc.y d.u (gm t) v := by
    by_contra hn
    exact hv0 (dif_neg hn)
  obtain ⟨v₀, dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩ := hex
  have hq : ∀ p, AnalyticAt ℂ (fun t' => gm t' p) t := fun p =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp hgma
  have hGa := MuPsh.analyticAt_eval hq pg
  have hHa := MuPsh.analyticAt_eval hq ph
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hmem : ∀ t' ∈ V, gm t' ∈ mcPts (mCoordIdeal Dc.y) := fun t' h =>
    (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie (gm t')).2 ⟨z t', Or.𝔐.all _, (hpt t' h).1⟩
  have hval0 : v₀ ≠ 0 := by
    have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y d.u (gm t) = v₀ :=
      valAt_eq (hmem t ht) ⟨dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩
    rwa [e1] at hv0
  have hg0 : MvPolynomial.eval (gm t) (MvPolynomial.map (Int.castRingHom ℂ) pg) ≠ 0 := by
    intro h
    apply hval0
    rw [hv₀, h, zero_div]
  let Fc : (Fin Dc.n → ℂ) → ℂ := fun t' =>
    MvPolynomial.eval (gm t') (MvPolynomial.map (Int.castRingHom ℂ) pg) /
      MvPolynomial.eval (gm t') (MvPolynomial.map (Int.castRingHom ℂ) ph) *
      ∏ k, gm t' ⟨k, d.c k⟩ ^ Hd.aMu k
  have hFc : AnalyticAt ℂ Fc t :=
    (hGa.div hHa hhne).mul (Finset.analyticAt_fun_prod _ fun k _ => (hq _).zpow (d.inDom.1 k))
  have hFc0 : Fc t ≠ 0 :=
    mul_ne_zero (div_ne_zero hg0 hhne) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (d.inDom.1 k))
  obtain ⟨G₀, hG₀, hlog⟩ := SheetPot.exists_log_norm_analytic (hFc.mul hQa) (mul_ne_zero hFc0 hQ0)
  let C : ℝ := (Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi)
  refine ⟨fun t' => G₀ t' + ((C / 2 : ℝ) : ℂ), hG₀.add analyticAt_const, ?_⟩
  have hdom : ∀ᶠ t' in 𝓝 t, InFrameDomain Dc.y d.c d.f (gm t') :=
    hgma.continuousAt.eventually (ChartGeo.inFrameDomain_eventually Dc.y d.c d.f d.inDom)
  filter_upwards [hxe, hV.mem_nhds ht, hQe, hlog, hdom, hHa.continuousAt.eventually_ne hhne,
    hFc.continuousAt.eventually_ne hFc0, hQa.continuousAt.eventually_ne hQ0] with
    t' ⟨v, hv, hf⟩ h1 ⟨hxpos, hsum⟩ hlg dom hph' hF1 hQ1
  obtain ⟨hco', hin', -⟩ := hpt t' h1
  obtain ⟨-, hall'⟩ := GlobalTheory.T.intersection_system_weight_right hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or (z t') (gm t') hco'
  let d' : MuFrameAt Hd (gm t') := { d with inDom := dom }
  obtain ⟨-, hP'⟩ := hall' d'
  obtain ⟨-, -, hform⟩ := hP' s hs
  have h2 := hform hin' (Γ' t') (hfib t' h1 v hv hf).2
  have hval' : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y d.u (gm t') =
      MvPolynomial.eval (gm t') (MvPolynomial.map (Int.castRingHom ℂ) pg) /
        MvPolynomial.eval (gm t') (MvPolynomial.map (Int.castRingHom ℂ) ph) :=
    valAt_eq (hmem t' h1) ⟨dg, pg, ph, hpg, hph, hne, heq, hph', rfl⟩
  have hn : ‖GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y d.u (gm t')‖ *
      ∏ k, ‖gm t' ⟨k, d.c k⟩‖ ^ Hd.aMu k = ‖Fc t'‖ := by
    simp only [Fc, norm_mul, norm_prod, norm_zpow, hval']
  have hsum' : ∑ τ, Real.log ((F.R t').gram (m := Dc.N - Dc.j) fun i => x τ i t').det.re =
      ballPot F.q t' + 2 * Real.log ‖Q t'‖ := hsum
  have hdet : ∀ τ, Real.log (Γ' t' τ).det.re = ((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi +
      Real.log ((F.R t').gram (m := Dc.N - Dc.j) fun i => x τ i t').det.re := fun τ => by
    have hxp : 0 < ((F.R t').gram (m := Dc.N - Dc.j) fun i => x τ i t').det.re := hxpos τ
    rw [hΓdet, Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hxp.ne', Real.log_pow]
  have hlg' : Real.log ‖Fc t' * Q t'‖ = (G₀ t').re := hlg
  rw [norm_mul (Fc t') (Q t'), Real.log_mul (norm_ne_zero_iff.2 hF1) (norm_ne_zero_iff.2 hQ1)] at hlg'
  have h3 : phMu Hd (gm t') = Real.log ‖Fc t'‖ + (∑ τ, Real.log (Γ' t' τ).det.re) / 2 := by
    rw [← hn]
    exact h2
  simp only [hdet, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum'] at h3
  rw [h3, Complex.add_re, ← hlg', Complex.ofReal_re]
  simp only [C]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp
