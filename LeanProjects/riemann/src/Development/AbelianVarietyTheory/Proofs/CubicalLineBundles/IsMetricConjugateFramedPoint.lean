import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyFieldStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatumStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonvaStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem isLieComb_of_two_pullbacks {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {x' : Sp S ⟶ X} (hx : x' = spMap f ≫ x) {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀]
    {G' : Over (Sp S)} [GrpObj G'] {φ : G₀.left ⟶ G.left} {φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G₀ G x φ) (h' : IsGrpPullback G' G x' φ') {n n' : ℕ} (hn : n' = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀} (hc : IsLieComb c v w)
    {v' : Fin n' → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ (v (i.cast hn)).left ≫ φ)
    (hw : w'.left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ w.left ≫ φ) :
    IsLieComb (fun i => f (c (i.cast hn))) v' w' := by
  subst hn
  subst hx
  have hw0 : φ' ≫ G.hom = (G'.hom ≫ spMap f) ≫ x := by rw [Category.assoc]; exact h'.1.w
  have hψ1 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ φ = φ' := h.1.lift_fst _ _ _
  have hψ2 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ G₀.hom = G'.hom ≫ spMap f := h.1.lift_snd _ _ _
  have hG : IsGrpPullback G' G₀ (spMap f) (h.1.lift φ' (G'.hom ≫ spMap f) hw0) :=
    IsGrpPullback.cancel h (IsGrpPullback.congr h' rfl hψ1.symm) hψ2
  have he : (algebraMap S (DualNumber S)).comp f = (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) := by
    clear h h' hv hw hc hG hψ1 hψ2 hw0
    first
    | exact RingHom.ext fun r => rfl
    | (ext r <;> simp [Chart.dualMapR] <;> rfl)
    | (ext r <;> simp [Chart.dualMapR] <;> erw [TrivSqZeroExt.algebraMap_eq_inl] <;> simp <;> done)
    | (ext r <;> simp [Chart.dualMapR] <;> simp [Algebra.algebraMap_eq_smul_one] <;> done)
    | (ext r
       · simp [Chart.dualMapR]
         show f r = f r
         rfl
       · simp [Chart.dualMapR]
         show (0 : S) = f 0
         simp)
  refine ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange f hG hc (fun i => ?_) ?_
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hv i, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w (v' i), Category.assoc, Over.w (v i)]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hw, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w w', Category.assoc, Over.w w]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])

theorem hermForm_map_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) (fun i => starRingEnd ℂ (z i)) (fun i => starRingEnd ℂ (w i)) =
      starRingEnd ℂ (hermForm Hm z w) := by
  unfold hermForm
  simp [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]

theorem isMetricAt_of_dim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (Φ : FibKey Xo ℂ x) (g : ℕ) (hg : Φ.key.P.g = g) (u : HolUnif Φ.key.P.A Φ.key.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ))
    (w : ∀ b : E →+* ℂ, Fin (Dw.mult b) → (epsR ℂ ⟶ Φ.key.P.A))
    (W : ∀ b : E →+* ℂ, Fin (Dw.mult b) → Fin g → ℂ)
    (h : SecTie Φ.m Φ.th s ∧ u.IsAH Hm χ ∧ u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧
      (∀ b i, (w b i).left ≫ Φ.m.φ = uu b i ∧ u.IsDiff (W b i) (w b i)) ∧
      ∀ b i k, Gr b i k = Real.pi * hermForm Hm (W b k) (W b i)) : IsMetricAt x s uu N Gr := by
  subst hg
  exact ⟨Φ, u, Hm, χ, θ, Fd, w, W, h⟩

theorem isMetricAt_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (hpq : 1 ≤ Dw.p + Dw.q) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x'))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (hx : x' = spMap (starRingEnd ℂ) ≫ x) (hs : SecBC (starRingEnd ℂ) 1 x x' s s') (hgen : SecGen x' s')
    (ht : ∀ τ i, IsTanAt x (uu τ i)) (ht' : ∀ τ i, IsTanAt x' (uu' τ i))
    (hu : ∀ τ i, uu' τ i = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ uu τ i)
    (h : IsMetricAt x s uu N Gr) : IsMetricAt x' s' uu' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, hT, hAH, hRig, hFn, hFd, hN, hw, hGr⟩ := h
  obtain ⟨Φ0⟩ := GlobalTheory.T.universalTripleFibreKeyData_nonempty_field E H Dw l Xo ℂ x' hpq
  have hNZ : SecNZ x' s' := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x' s' hgen
  obtain ⟨-, hex, huniq⟩ := GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing E H Dw l Xo ℂ x' Φ0.T.t Φ0.m
  obtain ⟨th, hth⟩ := hex s'
  have hne := ((huniq th s' hth).2).1 hNZ
  obtain ⟨hg, v', hv', hKey, hvrel⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (starRingEnd ℂ) x x' Φ
    { Φ0 with th := th, th_ne := hne } s s' hx hT hth hs
  obtain ⟨u', χ', θ', Fd', hAH', hRig', hFn', hFd', hNeq, hdiff⟩ :=
    GlobalTheory.T.exists_uniformisation_of_complexConjugate_keyDatum Φ.key _ hKey hg _ u Hm χ θ Fd ⟨hAH, hRig, hFn, hFd⟩
  have hpb : ∀ (Ψ : FibKey Xo ℂ x'), IsGrpPullback Ψ.T.t.G Xo.univ.t.G x' Ψ.m.φ := by
    intro Ψ
    exact Ψ.m.cart
  have hpb0 : IsGrpPullback Φ.T.t.G Xo.univ.t.G x Φ.m.φ := Φ.m.cart
  have hcomb : ∀ b i, ∃ cf : Fin Φ.T.g → ℂ, IsLieComb cf Φ.v (w b i) := by
    intro b i
    have hTB := ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x _ Φ.m.φ hpb0).2 _ Φ.v).1 Φ.basis
    obtain ⟨a, ha, -⟩ := hTB.2 _ (ht b i)
    refine ⟨a, (ReciprocityTheory.ChartRestriction.G.Chart.comb_push hpb0 a Φ.v (w b i)).2 ?_⟩
    rw [← (hw b i).1] at ha
    exact ha
  choose cf hcf using hcomb
  have hw' : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ0.T.t.G, w'.left ≫ Φ0.m.φ = uu' b i :=
    fun b i => (GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x' Φ0.T.t.G Φ0.m.φ (hpb Φ0)).1 _ (ht' b i)
  choose w' hw'e using hw'
  refine isMetricAt_of_dim x' s' uu' N _ _ _ hg u' (Hm.map (starRingEnd ℂ)) χ' θ' Fd' w'
    (fun b i k => starRingEnd ℂ (W b i k)) ⟨hth, hAH', hRig', hFn', hFd', ?_, fun b i => ⟨hw'e b i, ?_⟩, fun b i k => ?_⟩
  · rw [hN, hNeq]
  · exact hdiff (cf b i) (w b i) (w' b i) (W b i) (hcf b i)
      (isLieComb_of_two_pullbacks (starRingEnd ℂ) hx hpb0 (hpb _) hg (hcf b i) hvrel
        (by rw [hw'e, hu, (hw b i).1])) (hw b i).2
  · rw [Matrix.map_apply, hGr, map_mul, hermForm_map_conj]
    simp

theorem scal_one_mul_sec {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) (i : (PPx x).ι) :
    scal x 1 i * s.f i = s.f i := by
  simp only [scal]
  first
  | rw [map_one, one_mul]
  | simp [Out.liftFun]

theorem isMetric_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))) (N : ℝ) (Gr : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), 1 ≤ Dw.p + Dw.q → FrMap (FrameNorm.conjAlg σ) y y' → IsMetric y N Gr → IsMetric y' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr hpq hF hM
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  unfold IsMetric at hM ⊢
  refine isMetricAt_conj hpq y.x y'.x y.s y'.s y.u y'.u N Gr hx ?_ y'.gen y.tan y'.tan hu hM
  refine ⟨pm, h1, h2, fun i h => ?_⟩
  have h4 := h3 i h
  first
  | exact (congrArg _ (scal_one_mul_sec (S := ℂ) y.x y.s i)).trans h4
  | exact (congrArg _ (scal_one_mul_sec y.x y.s i)).trans h4
  | (convert h4 using 2; exact scal_one_mul_sec (S := ℂ) y.x y.s i)
  | (convert h4 using 2; simp only [scal]; first | rw [map_one, one_mul] | simp [Out.liftFun])
  | (erw [scal_one_mul_sec]; exact h4)

end GlobalTheory.LamT
