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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVectorStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange

noncomputable section

namespace GlobalTheory.MetricChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

theorem lift_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {G' : Over (Sp S)} [GrpObj G']
    {φ : G'.left ⟶ Xo.univ.t.G.left} (hp : IsGrpPullback G' Xo.univ.t.G x φ) :
    (∀ w : epsR S ⟶ G', IsTanAt x (w.left ≫ φ) → IsTangent w) ∧
    ∀ (n : ℕ) (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
      IsCombAt x (fun i => (v i).left ≫ φ) c w → ∃ w' : epsR S ⟶ G', w'.left ≫ φ = w ∧ IsLieComb c v w' := by
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  refine ⟨fun w h => hp.1.hom_ext ?_ ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  · refine (Category.assoc _ _ _).trans ?_
    rw [Over.w w, Over.w η[G']]
    exact zs
  · rintro n c v w ⟨u, hu, hw⟩
    refine ⟨(List.ofFn fun i => up (u i).left (Over.w _)).prod, (pr _).trans (Eq.trans ?_ hw),
      fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_, rfl⟩
    · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
        funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
      exact (congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this).symm
    · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
    · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
      exact (spMap_epsScaleR_comp (c i)).symm

def scaleSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := constFn p _ a * s.f i
  compat i j := by
    have h : ∀ (U V : X.Opens) (h : U ≤ V), (X.presheaf.map (homOfLE h).op).hom (constFn p V a) = constFn p U a := by
      intro U V h
      simp only [constFn]
      exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := V) (fun _ _ => trivial) (homOfLE h).op)
    rw [map_mul, map_mul, h, h, s.compat]
    ring

theorem nonzeroLocus_scaleSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (scaleSec p a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (constFn p (L.U k) a) := (ha.map _).map _
  show X.basicOpen (constFn p _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem hermForm_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (c d : Fin n → ℂ) :
    hermForm Hm (∑ l, c l • W l) (∑ j, d j • W j) = ∑ l, ∑ j, star (d j) * hermForm Hm (W l) (W j) * c l := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem metricAt_change {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ) (a : ℂ) (ha : a ≠ 0)
    (ht : ∀ b i, IsTanAt x (uu b i)) (hc : ∀ b i, IsCombAt x (uu b) (fun j => Y b j i) (uu' b i))
    (hs : SecBC (RingHom.id ℂ) a x x s s') (h : IsMetricAt x s uu N Gr) :
    IsMetricAt x s' uu' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨l1, l2⟩ := lift_comb Φ.m.cart
  have hw : ∀ b, uu b = fun i => (w b i).left ≫ Φ.m.φ := fun b => funext fun i => (h7 b i).1.symm
  have hx : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ.T.t.G, w'.left ≫ Φ.m.φ = uu' b i ∧ IsLieComb (fun j => Y b j i) (w b) w' :=
    fun b i => l2 _ _ (w b) _ (hw b ▸ hc b i)
  choose w' hw1 hw2 using hx
  let Φ' : FibKey Xo ℂ x :=
    { Φ with
      th := scaleSec Φ.T.t.G.hom a Φ.th
      th_ne := fun p => by rw [nonzeroLocus_scaleSec _ ha.isUnit]; exact Φ.th_ne p }
  refine ⟨Φ', u, Hm, χ, fun z => a * θ z, Fd, w', fun b i => ∑ j, Y b j i • W b j, ?_, h2, h3, ?_, h5, ?_,
    fun b i => ⟨hw1 b i, ?_⟩, fun b i k => ?_⟩
  · exact ((GlobalTheory.LamT.TieCalc.secTie_calc E H Dw l Xo ℂ x Φ.T.t Φ.m Φ.th s h1).1 a x s' _ rfl hs).2 fun _ => rfl
  · intro i z hz
    refine (valAt'_mul _ _ _ _).trans ?_
    rw [_root_.mul_assoc]
    exact congrArg₂ (· * ·) (valAt'_constFn _ _ (Over.w (u.ex z)) _ a hz) (h4 i z hz)
  · rw [h6, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [norm_mul, mul_pow, _root_.mul_assoc]
  · exact (GlobalTheory.T.tangentVector_existsUnique_uniformisingVector Φ.key u).2 _ (w b) (W b) _ (w' b i) (fun j => l1 _ ((h7 b j).1.symm ▸ ht b j))
      (fun j => (h7 b j).2) (hw2 b i)
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h8, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isMetric_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y y' : FrPt Xo c (CAt σ)) (N : ℝ) (Gr Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) (a : ℂ), a ≠ 0 → FrChg (S := CAt σ) (fun b => (Y b).transpose) a y y' → IsMetric y N Gr → IsMetric y' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr Y a ha ⟨hx, hc, hs⟩ h
  obtain ⟨x', hx', u', t', e', b', s', g'⟩ := y'
  obtain ⟨x, hx0, u, t, e, b, s, g⟩ := y
  obtain rfl : x' = x := hx
  exact metricAt_change x' s s' u u' N Gr Y a ha t hc hs h

end GlobalTheory.MetricChange
