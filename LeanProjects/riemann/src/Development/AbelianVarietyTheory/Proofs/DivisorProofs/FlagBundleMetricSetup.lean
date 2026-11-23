import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernDegreePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsAfterBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricChernIntegralEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameParahoricTransitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParahoricActionPreservesAdaptedFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameBaseChangeFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootDivisorsOfFrameBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyEmbedsComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGeometricallyConnectedStatement

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.CovTop GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagOverField

section Point

open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem chernIntegral_point {F : Type} [Field F] (σ : F →+* ℂ) {ι : Type} [Fintype ι] {m : ι → ℕ} (X : GlobalTheory.ProjVar.Var F)
    (E : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf X) m 0) (hX : X.dim = 0) :
    ∃ H : GlobalTheory.FlagBundle.Mat m X.Fn → CxPts X.str σ → GlobalTheory.FlagBundle.Mat m ℂ,
      IsMetricOn E ⊤ H ∧ IsGood E ⊤ H ∧ ∀ (R : MvPolynomial (ι × ℕ) ℝ) (t : ℝ), HasChernIntegral E ⊤ H R t →
        t = MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R := by
  obtain ⟨H, hH⟩ := SmoothMetric.exists_isMetricOn_top F σ X ι m E
  refine ⟨H, hH, fun y hy => absurd mem_ptsIn_top hy, fun R t ht => ?_⟩
  obtain ⟨⟨y⟩, hsub⟩ := GlobalTheory.Published.ArDegreeModel.unique_pt X σ hX
  have := X.smooth_str
  have := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
  have hV : Subsingleton (V X.dim) := by rw [hX]; infer_instance
  have hvol : (volume : Measure (V X.dim)) Set.univ = 1 := by
    have := (stdOrthonormalBasis ℝ (V X.dim)).volume_parallelepiped
    rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
      (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩] at this
  have hdet (i j : AlgChart X.str σ X.dim) (z : CxPts X.str σ) :
      transDet i.e j.e z = 1 := by
    rw [transDet, ContinuousLinearMap.det]
    exact LinearMap.det_eq_one_of_finrank_eq_zero (Module.finrank_zero_of_subsingleton (R := ℂ) (M := V X.dim)) _
  set r := MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R
  have hA : MeasurableSet (ptsIn X.str σ ⊤) := (isOpen_ptsIn _).measurableSet
  have hAs : ptsIn X.str σ ⊤ ⊆ c.e.source := fun z _ => Subsingleton.elim y z ▸ hc
  have hm (ε : ℤˣ) : chernTopPart E H R ε (ptsIn X.str σ ⊤) = ENNReal.ofReal ((ε : ℤ) * r) := by
    rw [chernTopPart, glueMeas_apply _ _ (fun i j => i.holo_trans j) ?_ c hA hAs,
      chartMeas_apply_of_subset _ _ hA hAs]
    · simp only [PointChern.chernTop_eq_eval hX]
      rw [show c.e '' ptsIn X.str σ ⊤ = Set.univ from
        Set.eq_univ_of_forall fun v => ⟨y, mem_ptsIn_top, Subsingleton.elim _ _⟩]
      simp [hvol, r]
    · intro i j z _ _
      simp [hdet, PointChern.chernTop_eq_eval hX]
  obtain ⟨-, h2⟩ := ht
  rw [← h2, Measure.real, Measure.real, hm, hm, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  push_cast
  rcases le_total 0 r with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

end Point

open GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.GoodMetric
open GlobalTheory.Twist (resM resM_self)

theorem isFrame_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ} [E.IsQuasicoherent]
    {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) {M : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (hM : IsUnit M.det) : IsFrame (pullCol π e hV M) := fun W h => by
  have hb := isFrame_pullbackSections π he (h.trans hV) W le_rfl
  have hN : IsUnit (M.map (resG Y h)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hM.map _
  have hc : Function.Bijective (M.map (resG Y h)).mulVec :=
    Function.bijective_iff_has_inverse.2 ⟨(M.map (resG Y h))⁻¹.mulVec,
      fun c => by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hN, Matrix.one_mulVec],
      fun c => by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, Matrix.one_mulVec]⟩
  convert hb.comp hc using 1
  funext c
  simp only [Function.comp_apply, Fintype.linearCombination_apply, res_pullCol, resM_self]
  simp only [pullCol, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

variable {F : Type} [Field F]

theorem isIso_str_pt : IsIso (proj F 0).str :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_proj_ι F 0) (GlobalTheory.ProjSpace.Model.isIso_str_zero (R := F))

theorem toPt_comp_str (Y : Var F) : toPt Y ≫ (proj F 0).str = Y.str := by
  have e : @inv _ _ _ _ (proj F 0).ι (isIso_proj_ι F 0) ≫ (proj F 0).str = PSpace.str F 0 := by
    haveI := isIso_proj_ι F 0
    exact IsIso.inv_hom_id_assoc (proj F 0).ι (PSpace.str F 0)
  rw [toPt, spToPt, Category.assoc, Category.assoc]
  erw [e]
  rw [ptF, GlobalTheory.ProjSpace.pt_str, show spMap (RingHom.id F) = 𝟙 _ from Spec.map_id _, Category.comp_id]

theorem exists_isHom_toPt (Y : Var F) :
    ∃ φ : (proj F 0).Fn →ₐ[F] Y.Fn, (ratOf (proj F 0)).IsHom (ratOf Y) φ (toPt Y) :=
  GlobalTheory.FlagBundle.exists_isHom_of_generic (ratOf (proj F 0)) (ratOf Y) (toPt Y) (toPt_comp_str Y)
    (GlobalTheory.FlagQ.eq_genericPoint_of_dim_zero (proj F 0) rfl _)

theorem keepsRad_toPt (Y : Var F) (φ : (proj F 0).Fn →ₐ[F] Y.Fn) (h : (ratOf (proj F 0)).IsHom (ratOf Y) φ (toPt Y)) :
    KeepsRad (ratOf (proj F 0)) (ratOf Y) φ (toPt Y) := by
  intro z g hg
  have hall (x : (proj F 0).Fn) : x ∈ (ratOf (proj F 0)).O (toPt Y z) := by
    have e : toPt Y z = genericPoint (ratOf (proj F 0)).Z := GlobalTheory.FlagQ.eq_genericPoint_of_dim_zero (proj F 0) rfl _
    exact ((congrArg (ratOf (proj F 0)).O e).trans (ratOf (proj F 0)).O_genericPoint).ge trivial
  refine ⟨(map_ne_zero φ).2 hg.1, h.map_mem_O (hall g), fun x n hx _ => ?_⟩
  rw [div_eq_mul_inv, ← map_inv₀]
  exact mul_mem hx (h.map_mem_O (hall g⁻¹))

variable {Y : Var F} {ι : Type} [Fintype ι] {r : ι → ℕ} {E : ι → (Sp F).Modules} {e : ∀ a, Fin (r a) → Γ(E a, ⊤)}
  {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)}

omit [Fintype ι] in

theorem par_of_mem_triv {z : (proj F 0).X} {A : Mat r (proj F 0).Fn} (hA : A ∈ (triv F r).S z) :
    Par 0 ((ratOf (proj F 0)).O z).toSubring A := by
  have e : A * (1 : Mat r (proj F 0).Fn)⁻¹ = A := by
    funext τ
    change A τ * (1 : Matrix _ _ _)⁻¹ = A τ
    rw [inv_one, mul_one]
  exact e ▸ hA

def adFr (hE : ∀ a, IsVB (E a) (r a)) (he : ∀ a, IsFrame (e a)) : Fr (ratOf Y) r r where
  S y := {A | AdFrame e fl y A}
  loc y := by
    obtain ⟨U, A, hy, hA⟩ := GlobalTheory.T.exists_local_adapted_frame_matrix F Y ι r E e fl hE he y
    have hd := (GlobalTheory.T.adapted_frame_parahoric_transition F Y ι r E e fl hE he y A (hA y hy)).1.det_ne
    refine ⟨U, A, hy, hd, fun z hz A' => ⟨(GlobalTheory.T.adapted_frame_parahoric_transition F Y ι r E e fl hE he z A (hA z hz)).2 A', fun h => ?_⟩⟩
    have := GlobalTheory.T.parahoric_action_preserves_adapted_frame F Y ι r E e fl hE he z A _ (hA z hz) h
    rwa [mul_assoc, Mat.inv_mul hd, mul_one] at this

theorem existsUnique_pt (hE : ∀ a, IsVB (E a) (r a)) (he : ∀ a, IsFrame (e a)) (hF : IsFlagBundle Y.str E r fl)
    (L : Type) [Field L] (x : Sp L ⟶ Sp F) (h : Mat r L) (hh : ∀ a, (h a).det ≠ 0) :
    ∃! p : Sp L ⟶ Y.X, p ≫ Y.str = x ∧ ∃ A', AdFrame e fl (p (IsLocalRing.closedPoint L)) A' ∧
      Par r ⊤ (h * (A'.map ((ratOf Y).val p))⁻¹) := by
  have hfl (a : ι) : ∃ fl' : Vert.Flag ((Scheme.Modules.pullback x).obj (E a)) (r a),
      Spans fl' ⊤ (pullCol x (e a) le_top ((h a).transpose.map (Scheme.ΓSpecIso (.of L)).inv.hom)) := by
    have := (hE a).isQuasicoherent
    refine exists_flag_spans_of_frame _ _ _ _ (isFrame_pullCol x (he a) _ ?_)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    exact (Ne.isUnit (hh a)).map _
  choose fl' hfl' using hfl
  obtain ⟨p, ⟨w, hp⟩, hu⟩ := hF _ x fl'
  refine ⟨p, ⟨w, ?_⟩, ?_⟩
  · obtain ⟨A', hA'⟩ := (adFr (fl := fl) hE he).nonempty (p (IsLocalRing.closedPoint L))
    exact ⟨A', hA', (GlobalTheory.T.adapted_frame_base_change_field_point F Y ι r E e fl hE he L p x w h fl' hfl' A' hA').1 hp⟩
  · rintro q ⟨w', A', hA', hP⟩
    exact hu q ⟨w', (GlobalTheory.T.adapted_frame_base_change_field_point F Y ι r E e fl hE he L q x w' h fl' hfl' A' hA').2 hP⟩

theorem refines_adFr (hE : ∀ a, IsVB (E a) (r a)) (he : ∀ a, IsFrame (e a)) (hF : IsFlagBundle Y.str E r fl)
    (φ : (proj F 0).Fn →ₐ[F] Y.Fn) (hφ : (ratOf (proj F 0)).IsHom (ratOf Y) φ (toPt Y)) :
    Refines (triv F r) (adFr (fl := fl) hE he) φ (toPt Y) := by
  refine ⟨fun _ => Nat.zero_le _, hφ, fun z A' hA' A hA => ?_, keepsRad_toPt Y φ hφ, fun L _ x A hA h hh => ?_⟩
  · exact (GlobalTheory.T.adapted_frame_parahoric_transition F Y ι r E e fl hE he z A' hA').1.mul
      ((par_of_mem_triv hA).map (φ : (proj F 0).Fn →+* Y.Fn) fun x hx => hφ.map_mem_O hx).inv
  have hA₀ := par_of_mem_triv hA
  have hc : Par 0 ⊤ (h * A.map ((ratOf (proj F 0)).val x)) :=
    hh.mul (hA₀.map_of _ (RatModel.valLoc (M := ratOf (proj F 0)) x _ specializes_rfl)
      fun z => (RatModel.valLoc_eq_val (M := ratOf (proj F 0)) x _ z).symm)
  refine (existsUnique_congr fun p => ?_).1 (existsUnique_pt hE he hF L (x ≫ (proj F 0).str) _ hc.det_ne)
  have := isIso_str_pt (F := F)
  have hx (p : Sp L ⟶ Y.X) (x : Sp L ⟶ (proj F 0).X) : p ≫ Y.str = x ≫ (proj F 0).str ↔ p ≫ toPt Y = x := by
    rw [← toPt_comp_str, ← Category.assoc, cancel_mono]
  refine (and_congr_left' (hx p x)).trans
    (and_congr_right fun hp => exists_congr fun A' => and_congr_right fun hA' => ?_)
  subst hp
  let ψ := RatModel.valLoc (M := ratOf Y) p (p (IsLocalRing.closedPoint L)) specializes_rfl
  have hψ (x : ((ratOf Y).O (p (IsLocalRing.closedPoint L))).toSubring) : (ratOf Y).val p x = ψ x :=
    (RatModel.valLoc_eq_val (M := ratOf Y) p _ x).symm
  have hB : Par 0 ((ratOf Y).O (p (IsLocalRing.closedPoint L))).toSubring (A.map φ) :=
    hA₀.map (φ : (proj F 0).Fn →+* Y.Fn) fun x hx => hφ.map_mem_O hx
  have ec : A.map ((ratOf (proj F 0)).val (p ≫ toPt Y)) = (A.map φ).map ((ratOf Y).val p) := by
    funext τ
    ext i k
    exact hφ.val_comp p _ ((hA₀ τ).1 i k)
  have hc' := hB.map_of _ ψ hψ
  have einv : (A.map φ)⁻¹.map ((ratOf Y).val p) = ((A.map φ).map ((ratOf Y).val p))⁻¹ := by
    have e := hB.inv.map_mul_of hB _ ψ hψ
    rw [Mat.inv_mul hB.det_ne] at e
    funext τ
    refine (Matrix.inv_eq_left_inv ?_).symm
    refine (congrFun e τ).symm.trans (Matrix.map_one _ ?_ ?_)
    · exact (hψ 0).trans (map_zero ψ)
    · exact (hψ 1).trans (map_one ψ)
  rw [(GlobalTheory.T.adapted_frame_parahoric_transition F Y ι r E e fl hE he _ A' hA').1.map_mul_of hB.inv _ ψ hψ, einv, Mat.mul_inv_rev,
    Mat.inv_inv hc'.det_ne, ← ec, ← mul_assoc]
  rfl

theorem exists_interPoly_eq (hG : GoodChernWeil) (σ : F →+* ℂ) (hE : ∀ a, IsVB (E a) (r a))
    (hF : IsFlagBundle Y.str E r fl) : ∃ gr : Root r → Y.Dv,
      (∀ x, toPic (gr x) = GlobalTheory.CechPic.cls ((fl x.1).root x.2) ((fl x.1).isLB_root x.2)) ∧
      ∀ (Q : MvPolynomial (Root r) ℝ) (c : ℝ), antisymm Q = c • rootDiscr r → Y.interPoly gr Q = c := by
  have hfr (a : ι) : ∃ e : Fin (r a) → Γ(E a, ⊤), IsFrame e := by
    obtain ⟨U, e, hx, he⟩ := hE a (IsLocalRing.closedPoint F)
    obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ =>
      Subsingleton.elim (α := PrimeSpectrum F) (IsLocalRing.closedPoint F) y ▸ hx
    exact ⟨e, he⟩
  choose e he using hfr
  obtain ⟨φ, hφ⟩ := exists_isHom_toPt Y
  obtain ⟨gr, h₁, h₂⟩ := GlobalTheory.T.exists_root_divisors_of_frame_bundle F Y ι r E e fl hE he (adFr hE he) fun _ _ => Iff.rfl
  refine ⟨gr, h₁, fun Q c hQ => ?_⟩
  obtain ⟨H, hH, hg, hT⟩ := chernIntegral_point σ (proj F 0) (triv F r) rfl
  have := hG.flag (refines_adFr hE he hF φ hφ) h₂ hH hg (Q := Q) (R := C c)
    (by rw [hQ, algHom_C, algebraMap_eq, C_mul'])
  rw [hT _ _ this, eval_C]

end GlobalTheory.FlagOverField

namespace GlobalTheory.FibreProj

open GlobalTheory.VB GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.FlagBaseChange GlobalTheory.CechPic GlobalTheory.Cartier

theorem isFlagBundle_sqFlag {B Y T P : Scheme.{0}} {f₁ : P ⟶ Y} {f₂ : P ⟶ T} {π : Y ⟶ B} {g : T ⟶ B}
    (hP : IsPullback f₁ f₂ π g) {ι : Type} {E : ι → B.Modules} {r : ι → ℕ}
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hfl : IsFlagBundle π E r fl) :
    IsFlagBundle f₂ (fun a => (Scheme.Modules.pullback g).obj (E a)) r fun a => sqFlag f₁ π f₂ g hP.w (fl a) := by
  intro T' h fl''
  obtain ⟨u, ⟨wu, hu⟩, huniq⟩ := hfl T' (h ≫ g)
    (fun a => (fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a)))
  obtain ⟨v, rfl, hv⟩ : ∃ v : T' ⟶ P, v ≫ f₁ = u ∧ v ≫ f₂ = h := ⟨hP.lift u h wu, hP.lift_fst _ _ _, hP.lift_snd _ _ _⟩
  refine ⟨v, ⟨hv, fun a i => (sqFlag_iff _ _ _ _ _ (fl a) v h hv wu (fl'' a) i).2 (hu a i)⟩, ?_⟩
  rintro v' ⟨hv', hprop⟩
  have w : (v' ≫ f₁) ≫ π = h ≫ g := by rw [Category.assoc, hP.w, ← Category.assoc, hv']
  exact hP.hom_ext (huniq _ ⟨w, fun a i => (sqFlag_iff _ _ _ _ hP.w (fl a) v' h hv' w (fl'' a) i).1 (hprop a i)⟩)
    (hv'.trans hv.symm)

theorem lbIso_root_sqFlag {B Y T P : Scheme.{0}} {f₁ : P ⟶ Y} {f₂ : P ⟶ T} {π : Y ⟶ B} {g : T ⟶ B}
    (w : f₁ ≫ π = f₂ ≫ g) {E : B.Modules} {n : ℕ} (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) (i : Fin n) :
    cls _ ((sqFlag f₁ π f₂ g w fl).isLB_root i) = cls _ (LB.isLB_pull (fl.isLB_root i) f₁) :=
  ((cls_eq_iff ((fl.isVB_gr i).pullback f₁).isLB_det _).2
    (((fl.isVB_gr i).pullback f₁).lbIso_det_of_iso (fl.pullGrIso f₁ i))).symm.trans
      ((cls_eq_iff _ _).2 ((fl.isVB_gr i).lbIso_det_pullback f₁)).symm

theorem isProjOver_id (F : Type) [Field F] : IsProjOver (𝟙 (Sp F)) := by
  have := GlobalTheory.ProjSpace.Model.isIso_str_zero (R := F)
  exact ⟨0, inv (PSpace.str F 0), inferInstance, IsIso.inv_hom_id _⟩

theorem exists_monomial_eq_prod_X {κ : Type} (n : ℕ) (m : κ →₀ ℕ) (hm : m.degree = n) :
    ∃ s : Fin n → κ, (monomial m 1 : MvPolynomial κ ℝ) = ∏ a, X (s a) := by
  subst hm
  have hl : m.toMultiset.toList.length = m.degree := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    rfl
  refine ⟨fun a => m.toMultiset.toList.get (a.cast hl.symm), ?_⟩
  refine Eq.trans ?_ ((finCongr hl.symm).prod_comp (fun a => (X (m.toMultiset.toList.get a) : MvPolynomial κ ℝ)) |>.trans
    (Fin.prod_univ_fun_getElem m.toMultiset.toList fun a => (X a : MvPolynomial κ ℝ))).symm
  rw [Multiset.prod_map_toList, ← prod_X_pow_eq_monomial, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
  rfl

theorem flag_mul_pull : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), IsArithVar q d → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (κ : Type) [Fintype κ] (A : κ → HermLB q) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial ((Σ a, Fin (r a)) ⊕ κ) ℝ →ₗ[ℝ] ℝ), IsArFun A d Φ → IsArFun (Sum.elim (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) fun a => (A a).pull π w) D Ψ → ∀ (P : MvPolynomial κ ℝ) (Q : MvPolynomial (Σ a, Fin (r a)) ℝ) (c : ℝ), P.IsHomogeneous (d + 1) → Q.IsHomogeneous (D - d) → GlobalTheory.GoodMetric.antisymm Q = c • GlobalTheory.GoodMetric.rootDiscr r → Ψ (rename Sum.inl Q * rename Sum.inr P) = c * Φ P := by
  intro hP k _ B Y _ _ q p d D hB hr hY π w ι _ E r h H fl hF κ _ A Φ Ψ hΦ hΨ P Q c hP' hQ hc
  have hE (a : ι) : IsVB (E a) (r a) := (h a).isVB
  have := hB.isNoetherianRing
  have := isNoetherian_of_isProjOver hB.isProjOver
  have hs := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hF
  generalize (∑ a, r a * (r a - 1) / 2) = n at hs
  obtain rfl : D = d + n := by
    have := hY.dim_eq.symm.trans (GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective B Y π n d
      (GlobalTheory.FlagSurj.isFlagBundle_surjective B Y π ι E r fl hE hF) hB.dim_eq)
    have h' : D + 1 = d + n + 1 := by exact_mod_cast this
    omega
  rw [Nat.add_sub_cancel_left] at hQ
  obtain ⟨σ⟩ := GlobalTheory.T.arithmetic_variety_embeds_complex k B q d hB
  let g : Sp B.functionField ⟶ B := B.fromSpecStalk (genericPoint B)
  have hE' (a : ι) := (hE a).pullback g
  have h₀ := IsPullback.of_hasPullback π g
  have hF₀ := isFlagBundle_sqFlag h₀ hF
  have := GlobalTheory.T.flag_bundle_geometrically_connected _ _ _ ι _ r _ hE' hF₀
  have : SmoothOfRelativeDimension n (Limits.pullback.snd π g) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension _) h₀ hs
  have hpr := GlobalTheory.FlagProj.isProjOver_of_isFlagBundle _ _ _ _ _ ι _ r _ (isProjOver_id B.functionField) hE' hF₀
  rw [Category.comp_id] at hpr
  obtain ⟨V, e, hd, he⟩ := Var.exists_iso (Limits.pullback.snd π g) n hpr
  subst hd
  have hj : IsPullback (e.inv ≫ Limits.pullback.fst π g) V.str π g :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Limits.pullback.condition, ← he, Category.assoc,
      e.inv_hom_id_assoc]⟩ e.symm rfl (by rw [Iso.symm_hom, ← he, e.inv_hom_id_assoc])
  generalize e.inv ≫ Limits.pullback.fst π g = j at hj
  obtain ⟨gr, hgr, hI⟩ := GlobalTheory.FlagOverField.exists_interPoly_eq hP.p16 σ hE' (isFlagBundle_sqFlag hj hF)
  rw [← hI Q c hc, Q.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨s, e₀⟩ := exists_monomial_eq_prod_X V.dim m (by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.1 hm))
  obtain ⟨Ψ', hΨ'⟩ := ((hP.p4.arExists k Y p _ hY).2 _ (Sum.elim
    (fun i => VMetric.grLB (fl (s i).1) (s i).2 ((H (s i).1).pull π w)) fun a => (A a).pull π w)).1
  have e₁ := GlobalTheory.T.arithmetic_variety_generic_fibre hP.p4 k B Y q p d V.dim hB hr hY π w V.X j V.str hj _ κ A Φ Ψ' hΦ hΨ' P hP'
  rw [VertForm.FormEx.arFun_eq_rename hP.p4 hY hΨ' hΨ (Sum.map s id) (by rintro (a | a) <;> rfl)] at e₁
  have e₂ := Var.inter_eq_of_toPic_eq (Δ := gr ∘ s) (fun i => LB.isLB_pull ((fl (s i).1).isLB_root (s i).2) j)
    fun i => (hgr (s i)).trans (lbIso_root_sqFlag hj.w (fl (s i).1) (s i).2)
  rw [show monomial m (coeff m Q) = coeff m Q • monomial m 1 by rw [smul_monomial, smul_eq_mul, mul_one], e₀, map_smul,
    smul_mul_assoc, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc, Var.interPoly_prod, e₂]
  congr 1
  refine Eq.trans (congrArg Ψ ?_) e₁
  simp [rename_rename, Function.comp_def]

end GlobalTheory.FibreProj
