import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormMulDetGram

noncomputable section

namespace GlobalTheory.DefPt.ThetaDeg

section Key

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.Frames GlobalTheory.CM
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem rule_frChg {κ : KeyRule} (hκ : IsKeyRule κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {K : Type} [Field K] [CharZero K] [Algebra c.F K] (M : Mats Dw K) (a : K) (y y' : FrPt Xo c K)
    (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x) (hb : FrChg M a y y') (hT : Tied e y.s y.u Φ)
    (hT' : Tied e y'.s y'.u Φ') :
    a ^ 8 * (κ K Φ'.key : K) = (∏ τ, (M τ).det) ^ 4 * (κ K Φ.key : K) := by
  classical
  obtain ⟨hx, hc, hs⟩ := hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hκ.2.1 K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hκ.1 K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    a _ hsc hcomb
  have e3 : ((Matrix.blockDiagonal' M).submatrix e e).det = ∏ τ, (M τ).det := by
    rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']
  exact e2.trans (congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1)

theorem hermForm_eq_zero (T : PAT H (Sp ℂ)) (u : HolUnif T.pol.A T.pol.L T.pol.g)
    {Hm : Matrix (Fin T.pol.g) (Fin T.pol.g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) {φ ψ : E →+* ℂ} (hne : φ ≠ ψ)
    {v w : epsR ℂ ⟶ T.t.G} {V W : Fin T.pol.g → ℂ} (tv : IsTangent v) (tw : IsTangent w) (hV : u.IsDiff V v)
    (hW : u.IsDiff W w) (ev : ∀ a : 𝓞 E, (v ≫ T.t.act.act a).left = spMap (epsMul (φ a)) ≫ v.left)
    (ew : ∀ a : 𝓞 E, (w ≫ T.t.act.act a).left = spMap (epsMul (ψ a)) ≫ w.left) : hermForm Hm V W = 0 := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT T.pol _ u Hm χ hAH
  choose ρ hρ using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom T.t.G T.t.G T.ab T.ab _ _ _ _ u u h1 h2
    (T.t.act.act s) (T.t.act.hom s)).imp fun _ h => h.1
  have hadj : ∀ a z w, hermForm Hm (ρ a z) w = hermForm Hm z (ρ (H.bar a) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL T.pol T.pol T.pol T.pol u u u u Hm Hm χ χ hAH hAH (T.t.act.act a) (𝟙 _) (𝟙 _)
      (T.t.act.act (H.bar a)) (ρ a) LinearMap.id LinearMap.id (ρ (H.bar a)) (hρ a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρ _)).1
      (weilEq_of_lamEq hL ℂ T.pol T.pol T.pol T.pol _ _ _ _ (T.t.act.hom a) inferInstance inferInstance
        (T.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact T.t.adj a))
  have key : ∀ {φ : E →+* ℂ} {v : epsR ℂ ⟶ T.t.G} {V : Fin T.pol.g → ℂ}, IsTangent v → u.IsDiff V v →
      (∀ a : 𝓞 E, (v ≫ T.t.act.act a).left = spMap (epsMul (φ a)) ≫ v.left) → ∀ a : 𝓞 E, ρ a V = φ a • V := by
    intro φ v V tv hV ev a
    have := T.t.act.hom a
    have h₁ := HomLinear.isDiff_comp u u (T.t.act.act a) (ρ a) (hρ a) tv hV
    have h₂ := CMCurveTest.isDiff_scaleVec u hV (φ a)
    have e : CMCurveTest.scaleVec (φ a) v = v ≫ T.t.act.act a := Over.OverMorphism.ext (ev a).symm
    rw [e] at h₂
    exact (h1 _ (HomLinear.isTangent_comp _ tv)).unique h₁ h₂
  by_contra h0
  refine hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))
  have h := hadj a V W
  rw [key tv hV ev, key tw hW ew, H.bar_eq, IsCMField.complexEmbedding_complexConj] at h
  simp only [hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, RCLike.star_def,
    Complex.conj_conj] at h h0
  exact mul_right_cancel₀ h0 h

theorem norm_rule_of_isMetricAt {κ : KeyRule} (hκ : IsKeyRule κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {x : Sp ℂ ⟶ Xo.X} {s : LB.Sec (PPx x)}
    {uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)} {N : ℝ}
    {φ : (E →+* ℂ) → (E →+* ℂ)} (hφ : Function.Injective φ) (tan : ∀ τ i, IsTanAt x (uu τ i))
    (eig : ∀ τ i (a : 𝓞 E), uu τ i ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (φ τ a)) ≫ uu τ i)
    (hB : TanBasis x fun j => uu (e j).1 (e j).2) (h : IsMetricAt x s uu N fun _ => 1) :
    ∃ Φ : FibKey Xo ℂ x, Tied e s uu Φ ∧ ‖(κ ℂ Φ.key : ℂ)‖ * N ^ 4 = (2 * Real.pi) ^ (2 * g) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, ht, hA, hR, hF, hD, hN, h7, h8⟩ := h
  obtain ⟨-, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x Φ.T.t.G Φ.m.φ Φ.m.cart
  have hv : IsLieBasis fun j => w (e j).1 (e j).2 := (hb _ _).2 (by
    rw [show (fun j => (w (e j).1 (e j).2).left ≫ Φ.m.φ) = fun j => uu (e j).1 (e j).2 from
      funext fun j => (h7 _ _).1]
    exact hB)
  obtain rfl : Φ.T.g = g := by
    simpa using Fintype.card_congr ((GlobalTheory.Serre.Lie.basis Φ.T.t.act Φ.basis).indexEquiv (GlobalTheory.Serre.Lie.basis Φ.T.t.act hv))
  refine ⟨{ Φ with v := _, basis := hv }, ⟨ht, rfl, fun j => (h7 _ _).1⟩, ?_⟩
  have ht' : ∀ b i, IsTangent (w b i) := fun b i =>
    (GlobalTheory.MetricChange.lift_comb Φ.m.cart).1 _ ((h7 b i).1.symm ▸ tan b i)
  have he : ∀ b i (a : 𝓞 E), (w b i ≫ Φ.T.t.act.act a).left =
      spMap (epsMul (φ b a)) ≫ (w b i).left := fun b i a => by
    refine Φ.m.cart.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, Φ.m.act a, ← Category.assoc, Category.assoc (spMap _)]
      exact (congrArg (· ≫ _) (h7 b i).1).trans ((eig b i a).trans (congrArg (_ ≫ ·) (h7 b i).1.symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (spMap_epsScaleR_comp _).symm
  let W' : Matrix (Fin Φ.T.g) (Fin Φ.T.g) ℂ := Matrix.of fun j => W (e j).1 (e j).2
  have hG : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W' j) (W' i)) = 1 := by
    ext i j
    obtain ⟨⟨b, i⟩, rfl⟩ := e.symm.surjective i
    obtain ⟨⟨b', j⟩, rfl⟩ := e.symm.surjective j
    have hW : ∀ p, W' (e.symm p) = W p.1 p.2 := fun p => by
      show W (e (e.symm p)).1 (e (e.symm p)).2 = _
      rw [e.apply_symm_apply]
    rw [Matrix.of_apply, hW, hW]
    by_cases hbb : b' = b
    · subst hbb
      rw [← h8]
      simp [Matrix.one_apply]
    · have hne : φ b' ≠ φ b := fun h => hbb (hφ h)
      rw [hermForm_eq_zero Φ.T u hA hne (ht' _ _) (ht' _ _) (h7 _ _).2 (h7 _ _).2 (he _ _) (he _ _), mul_zero,
        Matrix.one_apply_ne fun h => hbb (congrArg Sigma.fst (e.symm.injective h)).symm]
  have hdet := TopDifferential.det_gram Hm W'
  rw [hG, Matrix.det_one, Complex.one_re] at hdet
  obtain ⟨Ef, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all Φ.T.pol _ u Hm χ hA
  have := u.discrete
  have hvol := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 t₁ t₂ hD
  have h1 : (1 : ℝ) = (volume Fd).toReal / (Real.pi ^ Φ.T.g * ‖W'.det‖ ^ 2) := by
    rw [eq_inv_of_mul_eq_one_left hvol, eq_inv_of_mul_eq_one_left hdet.symm]
    exact (div_self (inv_ne_zero (right_ne_zero_of_mul_eq_one hvol))).symm
  have key := hκ.2.2.2.2 (FibKey.key { Φ with v := _, basis := hv }) u Hm W' χ θ Fd N 1 hA hR hF (fun j => (h7 _ _).2) hD hN h1
  rw [one_pow, mul_one] at key
  exact key

theorem norm_rule_of_isMetric {κ : KeyRule} (hκ : IsKeyRule κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) {N : ℝ} (h : IsMetric y N fun _ => 1) :
    ∃ Φ : FibKey Xo ℂ y.x, Tied (S := ℂ) e y.s y.u Φ ∧ ‖(κ ℂ Φ.key : ℂ)‖ * N ^ 4 = (2 * Real.pi) ^ (2 * g) :=
  norm_rule_of_isMetricAt hκ e (φ := fun b => σ.comp (embF c b))
    (fun _ _ h => RingHom.ext fun x => congrArg Subtype.val (σ.injective (RingHom.congr_fun h x))) y.tan y.eig
    ((GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c (CAt σ) y.x y.u g e y.tan y.eig).1 y.basis) h

end Key

section Places

open CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.FlatLine GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.KeyFourth
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.KeyIntegralVal
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem arch_clause {κ : KeyRule} (hκ : IsKeyRule κ) (hr : 1 ≤ Dw.p + Dw.q) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {y₀ : FrPt Xo c c.F} {Φ₀ : FibKey Xo c.F y₀.x}
    (h₀ : Tied e y₀.s y₀.u Φ₀) {σ : c.F →+* ℂ} {N : ℝ} {X : Mats Dw ℂ} (h : ArchFr y₀ σ N X) :
    4 * ∑ τ, Real.log ‖(X τ).det‖ + Real.log ‖σ (κ c.F Φ₀.key : c.F)‖ + 4 * Real.log N =
      2 * g * Real.log (2 * Real.pi) := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId _ _) y₀
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
    have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
    exact this
  obtain ⟨Φ, hΦ, hn⟩ := norm_rule_of_isMetric hκ e y (h.2.2 z y hz hy)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ z.x, Tied (S := ℂ) e z.s z.u Ψ :=
    @exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra z hr
  have e1 : (κ ℂ Ψ.key : ℂ) = σ (κ c.F Φ₀.key : c.F) := hκ.2.1 c.F ℂ σ _ _
    (@tied_keyPB E _ _ _ H Dw l Xo c g e c.F ℂ _ _ _ _ σ.toAlgebra (Algebra.ofId c.F (CAt σ)) y₀ z Φ₀ Ψ hz h₀ hΨ)
  have e2 := @rule_frChg E _ _ _ H Dw l Xo c κ hκ g e ℂ _ _ σ.toAlgebra (fun τ => (X τ)ᵀ) 1 z y Ψ Φ hy hΨ hΦ
  simp only [one_pow, one_mul, Matrix.det_transpose] at e2
  replace hn : ‖(∏ τ, (X τ).det) ^ 4 * σ (κ c.F Φ₀.key : c.F)‖ * N ^ 4 = (2 * Real.pi) ^ (2 * g) :=
    (congrArg (fun t : ℂ => ‖t‖ * N ^ 4) (e2.trans (congrArg (_ * ·) e1))).symm.trans hn
  rw [norm_mul, norm_pow, norm_prod] at hn
  have p1 : ∀ τ ∈ (Finset.univ : Finset (E →+* ℂ)), ‖(X τ).det‖ ≠ 0 := fun τ _ => norm_ne_zero_iff.2 (h.2.1 τ)
  have p2 := pow_ne_zero 4 (Finset.prod_ne_zero_iff.2 p1)
  have p3 : ‖σ (κ c.F Φ₀.key : c.F)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero σ).2 (Units.ne_zero _))
  have e3 := congrArg Real.log hn
  rw [Real.log_mul (mul_ne_zero p2 p3) (pow_ne_zero 4 h.1.ne'), Real.log_mul p2 p3, Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_prod p1] at e3
  push_cast at e3
  exact e3

theorem loc_clause {κ : KeyRule} (hκ : IsKeyRule κ) (hr : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {y₀ : FrPt Xo c c.F} {Φ₀ : FibKey Xo c.F y₀.x}
    (h₀ : Tied e y₀.s y₀.u Φ₀) {w : HeightOneSpectrum (𝓞 c.F)} {a : c.F} {B : Mats Dw c.F} (h : LocFr y₀ w a B) :
    4 * ∑ τ, (vAdd w (B τ).det : ℝ) + (vAdd w (κ c.F Φ₀.key : c.F) : ℝ) - 8 * (vAdd w a : ℝ) ≤
      4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  classical
  obtain ⟨T, io, ho, -, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F w
  letI := io.toAlgebra
  obtain ⟨y, z, hy, hz, hx⟩ := Model.exists_integral hr hg y₀ w T io 1 ho
  obtain ⟨Y, u₀, hY, hc⟩ := h.2.2 T io 1 ho y z hy hz hx
  choose τ' hτ using fun τ : E →+* ℂ => GlobalTheory.EtaVal.exists_base_map_of_overLa (β := embK c τ)
    (fun a => w.valuation_le_one (K := c.F) (RingOfIntegers.mapRingHom (embF c τ) a)) T io 1 ho
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨Φ, A, U, u, hΦ, a1, a2, hu⟩ := exists_tied_det hκ hr hg e ho τ' hτ y hy
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_mem_different_vLa (embF c τ) w
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult g e A U hinj (Embeddings.card E ℂ)
    inferInstance a1 a2 δ hδ
  have hb := (nval_bounds ho (fun τ => embF c τ (δ τ)) (fun τ => τ' τ (δ τ)) Dw.mult _ u
    (fun τ => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 (hδ0 τ))) (fun τ => hτ τ (δ τ)) hD).2
  rw [← hu, nval_of_ne (Units.ne_zero _), EReal.coe_le_coe_iff] at hb
  simp only [hδv, Int.cast_natCast, Nat.cast_one, div_one] at hb
  obtain ⟨Ψ, hΨ⟩ := exists_tied E H Dw l Xo c g e T.Fr z hr
  have e1 : (κ T.Fr Ψ.key : T.Fr) = io (κ c.F Φ₀.key : c.F) := hκ.2.1 c.F T.Fr io _ _
    (tied_keyPB E H Dw l Xo c g e c.F T.Fr (Algebra.ofId c.F T.Fr) y₀ z Φ₀ Ψ hz h₀ hΨ)
  have e2 := rule_frChg hκ e _ _ z y Ψ Φ hc hΨ hΦ
  simp only [Matrix.det_transpose, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e2
  have key : ∀ (s : c.F) (v : T.V), s ≠ 0 → IsUnit v → vV T.V (io s * algebraMap T.V T.Fr v) = vAdd w s := by
    intro s v hs hv
    rw [vV_mul ((map_ne_zero io).2 hs) (hv.map _).ne_zero, ho.2]
    simp [vV, valV_algebraMap_unit T hv, vLa, vAdd]
  have ne : ∀ (s : c.F) (v : T.V), s ≠ 0 → IsUnit v → io s * algebraMap T.V T.Fr v ≠ 0 := fun s v hs hv =>
    mul_ne_zero ((map_ne_zero io).2 hs) (hv.map _).ne_zero
  have pw : ∀ (a : T.Fr) (k : ℕ), vV T.V (a ^ k) = k * vV T.V a := fun a k => by simp [vV]
  have hp : ∀ s : Finset (E →+* ℂ), vV T.V (∏ τ ∈ s, io (B τ).det * algebraMap T.V T.Fr (Y τ).det) =
      ∑ τ ∈ s, vAdd w (B τ).det := fun s => by
    induction s using Finset.induction_on with
    | empty => simp [vV]
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ, vV_mul (ne _ _ (h.2.1 τ) (hY τ))
        (Finset.prod_ne_zero_iff.2 fun i _ => ne _ _ (h.2.1 i) (hY i)), ih, key _ _ (h.2.1 τ) (hY τ)]
  have e3 := congrArg (vV T.V) e2
  rw [vV_mul (pow_ne_zero _ (ne _ _ h.1 u₀.isUnit)) (Units.ne_zero _), vV_mul (pow_ne_zero _
    (Finset.prod_ne_zero_iff.2 fun i _ => ne _ _ (h.2.1 i) (hY i))) (Units.ne_zero _), pw, pw, hp,
    key _ _ h.1 u₀.isUnit, e1, ho.2] at e3
  have e4 : (8 : ℝ) * (vAdd w a : ℝ) + (vV T.V (κ T.Fr Φ.key : T.Fr) : ℝ) =
      4 * ∑ τ, (vAdd w (B τ).det : ℝ) + (vAdd w (κ c.F Φ₀.key : c.F) : ℝ) := by
    rw [Nat.cast_one, one_mul] at e3
    exact_mod_cast e3
  linarith

theorem lineDeg_le {K : Type} [Field K] [NumberField K] {J : Type} [Fintype J] {k : K} (hk : k ≠ 0)
    (a : HeightOneSpectrum (𝓞 K) → ℝ) (b o : J → HeightOneSpectrum (𝓞 K) → ℝ) (m : J → ℝ) (N : (K →+* ℂ) → ℝ)
    (x : J → (K →+* ℂ) → ℝ) (C L : ℝ) (hN : ∀ σ, 0 < N σ) (ha : (Function.support a).Finite)
    (hb : ∀ j, (Function.support (b j)).Finite) (ho : ∀ j, (Function.support (o j)).Finite)
    (hL : ∀ j, ∑ᶠ w, o j w * lw K w = L)
    (h₁ : ∀ σ, 4 * ∑ j, Real.log (x j σ) + Real.log ‖σ k‖ + 4 * Real.log (N σ) = C)
    (h₂ : ∀ w, 4 * ∑ j, b j w + (vAdd w k : ℝ) - 8 * a w ≤ 4 * ∑ j, m j * o j w) :
    (∑ j, lineDeg (x j) (b j)) / 2 + C / 8 - (∑ j, m j) * L / 2 ≤ lineDeg (fun σ => (Real.sqrt (N σ))⁻¹) a := by
  classical
  have hK : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have hS := (ha.union (finite_vAdd hk)).union ((Set.finite_iUnion hb).union (Set.finite_iUnion ho))
  have fs : ∀ f : HeightOneSpectrum (𝓞 K) → ℝ, Function.support f ⊆ hS.toFinset →
      ∑ᶠ w, f w * lw K w = ∑ w ∈ hS.toFinset, f w * lw K w := fun f hf =>
    finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_left _ _).trans hf)
  have s1 := fs a (by rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inl (Or.inl h))
  have s2 := fs (fun w => (vAdd w k : ℝ)) (by rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inl (Or.inr h))
  have s3 := fun j => fs (b j) (by
    rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inr (Or.inl (Set.mem_iUnion.2 ⟨j, h⟩)))
  have s4 := fun j => (hL j).symm.trans (fs (o j) (by
    rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, h⟩))))
  have h0 := lineDeg_num hk
  unfold lineDeg at h0 ⊢
  simp only [s1, s2, s3] at h0 ⊢
  generalize hS.toFinset = S at *
  have t1 : 4 * ∑ j, ∑ w ∈ S, b j w * lw K w + ∑ w ∈ S, (vAdd w k : ℝ) * lw K w - 8 * ∑ w ∈ S, a w * lw K w ≤
      4 * ((∑ j, m j) * L) := by
    have := Finset.sum_le_sum (s := S) fun w _ => mul_le_mul_of_nonneg_right (h₂ w)
      (show 0 ≤ lw K w from div_nonneg (Real.log_natCast_nonneg _) hK.le)
    simp only [sub_mul, add_mul, mul_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_mul] at this
    rw [Finset.sum_comm (s := S), Finset.sum_comm (s := S)] at this
    simp only [← Finset.mul_sum, ← s4] at this
    rwa [Finset.sum_mul]
  have t2 : 4 * ∑ j, (∑ σ, Real.log (x j σ)) / (Module.finrank ℚ K : ℝ) +
      (∑ σ : K →+* ℂ, Real.log ‖σ k‖) / (Module.finrank ℚ K : ℝ) +
      4 * ((∑ σ, Real.log (N σ)) / (Module.finrank ℚ K : ℝ)) = C := by
    have := Finset.sum_congr (s₁ := Finset.univ) rfl fun σ _ => h₁ σ
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Embeddings.card,
      nsmul_eq_mul] at this
    rw [Finset.sum_comm] at this
    rw [← Finset.sum_div]
    field_simp
    linarith
  have t3 : ∑ σ, Real.log (Real.sqrt (N σ))⁻¹ = -(1 / 2) * ∑ σ, Real.log (N σ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [Real.log_inv, Real.log_sqrt (hN σ).le]; ring
  rw [t3, Finset.sum_sub_distrib, mul_div_assoc (-(1 / 2) : ℝ)]
  linarith

end Places

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∑ τ : Psi H, P.degLie τ.1) / 2 + ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) ≤ P.degTh := by
  intro E _ _ _ H Dw l Xo c r U ξ h Z P
  have hr : 1 ≤ Dw.p + Dw.q := h.p.trans (Nat.le_add_right _ _)
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c _ e c.F P.y₀ hr
  have key := lineDeg_le (κ c.F Φ₀.key).ne_zero (fun w => (vAdd w (P.a w) : ℝ))
    (fun τ w => (vAdd w (P.B w τ).det : ℝ))
    (fun τ w => (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.ord_vw w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.conjDifferent (embF c τ)) : ℝ)) (fun τ => (Dw.mult τ : ℝ)) P.N
    (fun τ σ => ‖(P.X σ τ).det‖) _ _ (fun σ => (P.arch σ).1)
    (P.fin.subset fun w hw h' => hw (by simp [h'.1, vAdd]))
    (fun τ => P.fin.subset fun w hw h' => hw (by simp [h'.2, vAdd]))
    (fun τ => finite_ord _) (fun τ => sum_ord _) (fun σ => arch_clause hκ hr e h₀ (P.arch σ))
    (fun w => loc_clause hκ hr h.good e h₀ (P.loc w))
  have hsub : ∀ f : (E →+* ℂ) → ℝ, (∀ τ, Dw.mult τ = 0 → f τ = 0) → ∑ τ, f τ = ∑ τ : Psi H, f τ.1 := fun f hf => by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0) f,
      Finset.sum_eq_zero (s := Finset.univ) (f := fun τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} => f τ.1)
        fun τ _ => hf _ (by rw [Datum.mult, if_neg τ.2, h.q]), add_zero]
    convert rfl
  have h1 : ∑ τ, (Dw.mult τ : ℝ) = (Fintype.card (Psi H) : ℝ) * Dw.p := by
    rw [hsub _ fun τ h => by rw [h, Nat.cast_zero],
      Finset.sum_congr rfl fun (τ : Psi H) _ => show (Dw.mult τ.1 : ℝ) = Dw.p by rw [Datum.mult, if_pos τ.2]]
    simp
  have h2 : (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : ℝ) = (Fintype.card (Psi H) : ℝ) * Dw.p := by
    rw [← h1]; simp [Fintype.card_sigma]
  have h3 : ∑ τ, P.degLie τ = ∑ τ : Psi H, P.degLie τ.1 := hsub _ fun τ h => by
    have : IsEmpty (Fin (Dw.mult τ)) := by rw [h]; infer_instance
    simp [PtData.degLie, detDeg, lineDeg, vAdd]
  rw [h1, h2] at key
  rw [← h3]
  change (∑ τ, P.degLie τ) / 2 + _ - _ ≤ P.degTh at key
  linarith

end GlobalTheory.DefPt.ThetaDeg

end
