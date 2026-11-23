import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBasisNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CochGram

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieCoord lieAdd)
open GlobalTheory.TorusLieCoord GlobalTheory.CxPts Formalism.L2.Pj

theorem exists_uniform {X : Type} [TopologicalSpace X] [CompactSpace X] {n : Type} [Fintype n] [DecidableEq n]
    (F : X → Matrix n n ℂ) (hF : ∀ a b, Continuous fun z => F z a b) (hP : ∀ z, (F z).PosDef) :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ z, ((C : ℂ) • F z - 1).PosSemidef := by
  have hS : IsCompact ((Set.univ : Set X) ×ˢ Metric.sphere (0 : n → ℂ) 1) :=
    isCompact_univ.prod (isCompact_sphere 0 1)
  have hq : Continuous fun p : X × (n → ℂ) => (star p.2 ⬝ᵥ F p.1 *ᵥ p.2).re := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine Complex.continuous_re.comp (continuous_finset_sum _ fun j _ => ?_)
    refine Continuous.mul ((continuous_apply j).comp continuous_snd).star (continuous_finset_sum _ fun k _ => ?_)
    exact ((hF j k).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)
  obtain ⟨m, hm, hmin⟩ := hS.exists_forall_le' hq.continuousOn (a := 0) fun p hp => by
    have h2 : p.2 ≠ 0 := fun h0 => by simpa [h0] using hp.2
    exact (Complex.pos_iff.1 ((hP p.1).dotProduct_mulVec_pos h2)).1
  refine ⟨Fintype.card n / m, fun C hC z => ?_⟩
  have hH : ((C : ℂ) • F z - 1).IsHermitian := by
    refine IsHermitian.sub ?_ isHermitian_one
    rw [IsHermitian, conjTranspose_smul, (hP z).isHermitian.eq]
    simp
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun v => ?_⟩
  refine Complex.nonneg_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
  have hvv : (star v ⬝ᵥ v).re ≤ Fintype.card n * ‖v‖ ^ 2 := by
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    calc ∑ i, (star (v i) * v i).re ≤ ∑ _i : n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = _ := by simp
  have hq1 : m * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ F z *ᵥ v).re := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 := hmin (z, ((‖v‖⁻¹ : ℝ) : ℂ) • v) ⟨trivial, by simp [norm_smul, hn.ne']⟩
    simp only [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal, Complex.re_ofReal_mul] at h1
    rw [← _root_.mul_assoc, ← mul_inv, le_inv_mul_iff₀ (by positivity)] at h1
    nlinarith
  rw [sub_mulVec, dotProduct_sub, one_mulVec, smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.sub_re,
    Complex.re_ofReal_mul]
  have hC' : (Fintype.card n : ℝ) ≤ C * m := (div_le_iff₀ hm).1 hC
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  nlinarith [mul_le_mul_of_nonneg_left hq1 hC0, mul_le_mul_of_nonneg_right hC' (sq_nonneg ‖v‖)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {r : ℕ}

section Lin

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : torus R r ⟶ (Over.pullback x).obj t.G) [IsMonHom v]

def img (e : LieG (torus R r)) : TanM x t.G :=
  mkT (pushHom (isGrpPullback_pullback t.G x) (epsR R) (e.1 ≫ v))
    ((isTangent_iff (isGrpPullback_pullback t.G x) _).1 (by
      have h := congrArg (fun q => q.left) (IndefiniteRowSideFullHecke.LieAlgebraMaps.lieMap v e).2
      refine h.trans ?_
      have e1 : (toUnit (specO R R)).left = 𝟙 _ :=
        (Category.comp_id _).symm.trans ((Over.w (toUnit (specO R R))).trans (Spec.map_id _))
      rw [Over.comp_left, e1]
      exact Category.id_comp _))

theorem left_img (e : LieG (torus R r)) : (tv (img v e)).left = e.1.left ≫ v.left ≫ pullback.fst t.G.hom x :=
  Category.assoc _ _ _

def vecOf (c : Fin r → R) : LieG (torus R r) := ⟨pt c, pt_mem c⟩

theorem lieCoord_vecOf (c : Fin r → R) : lieCoord (vecOf c) = c := by
  funext i
  change (valA (pt c) (Pi.single i 1)).snd = c i
  rw [valA_pt]
  simp [TorusLieCoord.linForm, Pi.single_apply]

def dif : (Fin r → R) →ₗ[R] TanM x t.G where
  toFun c := img v (vecOf c)
  map_add' c d := by
    have e : vecOf (c + d) = lieAdd _ (vecOf c) (vecOf d) := (lieCoord_bijective_add_smul R r).1.1 (by
      rw [(lieCoord_bijective_add_smul R r).2.1, lieCoord_vecOf, lieCoord_vecOf, lieCoord_vecOf])
    rw [e]
    refine tanM_ext ?_
    exact (congrArg (pushHom (isGrpPullback_pullback t.G x) (epsR R)) (MonObj.mul_comp _ _ v)).trans (map_mul _ _ _)
  map_smul' a c := by
    have e : vecOf (a • c) = AvDefs.lieScale _ a (vecOf c) := (lieCoord_bijective_add_smul R r).1.1 (by
      rw [(lieCoord_bijective_add_smul R r).2.2, lieCoord_vecOf, lieCoord_vecOf])
    rw [e]
    refine tan_ext ((left_img _ _).trans ?_)
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (left_img v (vecOf c)).symm)

theorem dif_injective [Mono v] : Function.Injective (dif v) := fun c d h => by
  have h1 : (vecOf c).1 ≫ v = (vecOf d).1 ≫ v := push_inj (isGrpPullback_pullback t.G x) (congrArg tv h)
  rw [← lieCoord_vecOf c, Subtype.ext ((cancel_mono v).1 h1), lieCoord_vecOf]

end Lin

theorem linearIndependent_of_isCochFrame {R : Type} [CommRing R] {x : Sp R ⟶ X} {ε : Fin r → TanM x t.G}
    (h : IsCochFrame t x ε) : LinearIndependent R ε := by
  obtain ⟨v, hv, hc, h⟩ := h
  have : Mono v := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono v.left))
  have e : ε = dif v ∘ Pi.basisFun R (Fin r) := funext fun i => by
    obtain ⟨e, he, h⟩ := h i
    have : e = vecOf (Pi.basisFun R (Fin r) i) := (lieCoord_bijective_add_smul R r).1.1 (by
      rw [he, lieCoord_vecOf, Pi.basisFun_apply])
    subst this
    exact tan_ext (h.trans (left_img v _).symm)
  rw [e]
  exact (Pi.basisFun R (Fin r)).linearIndependent.map' _ (LinearMap.ker_eq_bot.2 (dif_injective v))

section Family

variable {W : Scheme.{0}} {g : W ⟶ X} (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback g).obj t.G)
  {R R' : Type} [CommRing R] [CommRing R']

theorem exists_fibHom [IsMonHom u] (w : Sp R ⟶ W) : ∃ v : torus R r ⟶ (Over.pullback (w ≫ g)).obj t.G, IsMonHom v ∧
    v.left ≫ pullback.fst t.G.hom (w ≫ g) = SplitTorus.bcMap w _ ≫ u.left ≫ pullback.fst t.G.hom g ∧
    (IsClosedImmersion ((Over.pullback w).map u).left → IsClosedImmersion v.left) := by
  obtain ⟨e, he, h⟩ := grpPullback_iso ((isGrpPullback_pullback _ w).comp (isGrpPullback_pullback t.G g))
    (isGrpPullback_pullback t.G (w ≫ g))
  refine ⟨(SplitTorus.bcIso w _).hom ≫ (Over.pullback w).map u ≫ e.hom, inferInstance, ?_, fun hc => ?_⟩
  · have A : ((Over.pullback w).map u).left ≫ pullback.fst _ w = pullback.fst _ w ≫ u.left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h, reassoc_of% A,
      SplitTorus.bcIso_hom_fst_assoc]
  · rw [Over.comp_left, Over.comp_left]
    have : IsIso (SplitTorus.bcIso w (Fin r → ℤ)).hom.left := ((Over.forget _).mapIso (SplitTorus.bcIso w _)).isIso_hom
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    have h₁ : IsClosedImmersion (((Over.pullback w).map u).left ≫ e.hom.left) :=
      (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).2 hc
    exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).2 h₁

def raw (w : Sp R ⟶ W) (i : Fin r) : Sp (DualNumber R) ⟶ t.G.left :=
  (pt (Pi.single i 1 : Fin r → R)).left ≫ SplitTorus.bcMap w _ ≫ u.left ≫ pullback.fst t.G.hom g

theorem isTan_raw [IsMonHom u] {w : Sp R ⟶ W} {x : Sp R ⟶ X} (hx : w ≫ g = x) (i : Fin r) :
    IsTanAtG t x (raw u w i) := by
  subst hx
  obtain ⟨v, hv, h, -⟩ := exists_fibHom u w
  have := isTan_tv (img v (vecOf (Pi.single i 1)))
  rwa [left_img, h] at this

theorem appTop_pt (c : Fin r → R) (a : Fin r → ℤ) :
    (pt c).left.appTop.hom (Rosenlicht.chi _ a) = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom
      (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (TorusLieCoord.linForm c a)) := by
  rw [← valA_pt, valA, SplitTorus.charUnit_val]
  exact ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom_inv_id_apply _).symm

theorem dual_pt (φ : R →+* R') (w : Sp R ⟶ W) (c : Fin r → R) :
    spMap (dualMap φ) ≫ (pt c).left ≫ SplitTorus.bcMap w _ =
      (pt (φ ∘ c)).left ≫ SplitTorus.bcMap (spMap φ ≫ w) (Fin r → ℤ) := by
  let T : Over W := Over.mk (spMap (algebraMap R' (DualNumber R')) ≫ spMap φ ≫ w)
  let a : T ⟶ splitTorus W (Fin r → ℤ) := Over.homMk (spMap (dualMap φ) ≫ (pt c).left ≫ SplitTorus.bcMap w _) (by
    rw [Category.assoc, Category.assoc, SplitTorus.bcMap_hom, Over.w_assoc (pt c)]
    show spMap _ ≫ spMap _ ≫ w = spMap _ ≫ spMap _ ≫ w
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, PullbackSections.dualMap_comp_alg])
  let b : T ⟶ splitTorus W (Fin r → ℤ) := Over.homMk ((pt (φ ∘ c)).left ≫ SplitTorus.bcMap (spMap φ ≫ w) _) (by
    rw [Category.assoc, SplitTorus.bcMap_hom, Over.w_assoc (pt (φ ∘ c))]
    rfl)
  refine congrArg (fun q => q.left) (SplitTorus.hom_ext (g := a) (g' := b) fun χ => ?_)
  rw [SplitTorus.val_eq, SplitTorus.val_eq]
  show (spMap (dualMap φ) ≫ (pt c).left ≫ SplitTorus.bcMap w _).appTop.hom _ =
    ((pt (φ ∘ c)).left ≫ SplitTorus.bcMap (spMap φ ≫ w) _).appTop.hom _
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, SplitTorus.bcMap_appTop_chi, appTop_pt]
  refine (congrArg _ (appTop_pt c χ)).trans ?_
  refine (SplitTorus.specMap_appTop_apply (CommRingCat.ofHom (dualMap φ)) _).trans (congrArg _ ?_)
  ext <;> simp [dualMap, TorusLieCoord.linForm]

theorem dual_raw (φ : R →+* R') (w : Sp R ⟶ W) (i : Fin r) :
    spMap (dualMap φ) ≫ raw u w i = raw u (spMap φ ≫ w) i := by
  have e : φ ∘ (Pi.single i 1 : Fin r → R) = Pi.single i 1 := funext fun j => by
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [raw, raw, ← e, reassoc_of% (dual_pt φ w (Pi.single i 1))]

variable [IsMonHom u]

def coch (w : Sp R ⟶ W) {x : Sp R ⟶ X} (hx : w ≫ g = x) (i : Fin r) : TanM x t.G := tanOf (isTan_raw u hx i)

theorem isCochFrame_coch {w : Sp R ⟶ W} {x : Sp R ⟶ X} (hx : w ≫ g = x)
    (hc : IsClosedImmersion ((Over.pullback w).map u).left) : IsCochFrame t x (coch u w hx) := by
  subst hx
  obtain ⟨v, hv, h, hc'⟩ := exists_fibHom u w
  exact ⟨v, hv, hc' hc, fun i => ⟨vecOf (Pi.single i 1), lieCoord_vecOf _, by rw [h]; rfl⟩⟩

end Family

section Cont

variable {Z W : Scheme.{0}} (f : Z ⟶ X) (π : W ⟶ Z) {k : Type} [CommRing k] {p : Z ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

def down (y : CxPts (π ≫ p) σ) : CxPts p σ := ⟨y.1 ≫ π, (Category.assoc _ _ _).trans y.2⟩

theorem exists_basis (z : CxPts p σ) : ∃ (V : Z.affineOpens) (n : ℕ) (v : Fin n → TanM (LogKS.chart V ≫ f) t.G),
    z ∈ ptsIn p σ V.1 ∧ LieLocFrame.IsBasis v := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := z.1 (IsLocalRing.closedPoint ℂ)) trivial
  have h₀ : z ∈ ptsIn p σ U := mem_ptsIn.2 hyU
  obtain ⟨g, hg, hb⟩ := LieLocFrame.exists_isBasis_near t (LogKS.chart ⟨U, hU⟩ ≫ f) (evHom h₀)
  let V : Z.affineOpens := ⟨Z.basicOpen g, hU.basicOpen g⟩
  have hVU : V.1 ≤ U := Z.basicOpen_le g
  obtain ⟨n, v, hv⟩ := hb Γ(Z, V.1) (resG Z hVU) (LogKS.chart V ≫ f) (Z.toRingedSpace.isUnit_res_basicOpen g)
    (LieLocFrame.spMap_res_chart f (V := ⟨U, hU⟩) hVU)
  exact ⟨V, n, v, (mem_ptsIn_basicOpen h₀ g).2 (by rwa [ev_eq h₀]), hv⟩

theorem continuous_gram {A : AnRead p σ d}
    {h : ∀ y : CxPts p σ, TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ} (hh : IsLieMetric t f A h)
    (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback (π ≫ f)).obj t.G) [IsMonHom u] (a b : Fin r) :
    Continuous fun y : CxPts (π ≫ p) σ =>
      gramOf (h (down π y)) (coch u y.1 (Category.assoc _ _ _).symm) a b := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  have hd : Continuous (down π (p := p) (σ := σ)) := continuous_of_comp (f := π) fun _ => rfl
  obtain ⟨V, n, v, hV, hv⟩ := exists_basis (t := t) f (down π y₀)
  obtain ⟨O, hO, hyO, hle⟩ := exists_isAffineOpen_mem_and_subset (X := W) (U := π ⁻¹ᵁ V.1)
    (x := y₀.1 (IsLocalRing.closedPoint ℂ)) (mem_ptsIn.1 ((mem_ptsIn_preimage (f := π) fun _ => rfl).2 hV))
  have hle' : O ≤ π ⁻¹ᵁ V.1 := hle
  have hψ : spMap (π.appLE V.1 O hle').hom ≫ LogKS.chart V = LogKS.chart ⟨O, hO⟩ ≫ π :=
    IsAffineOpen.SpecMap_appLE_fromSpec π V.2 hO hle'
  have hψ' : spMap (π.appLE V.1 O hle').hom ≫ LogKS.chart V ≫ f = LogKS.chart ⟨O, hO⟩ ≫ π ≫ f := by
    rw [reassoc_of% hψ]
  choose c hc using fun i => (hv.res _ hψ' (coch u (LogKS.chart ⟨O, hO⟩) rfl i)).exists
  choose G hG₁ hG₂ hG using fun i j => hh.2 V (v i) (v j)
  have hmem : ∀ y ∈ ptsIn (π ≫ p) σ O, down π y ∈ ptsIn p σ V.1 := fun y hy =>
    (mem_ptsIn_preimage (f := π) fun _ => rfl).1 (ptsIn_mono hle' hy)
  have key : ∀ y (hy : y ∈ ptsIn (π ≫ p) σ O) (i : Fin r),
      coch u y.1 (x := (down π y).1 ≫ f) (Category.assoc _ _ _).symm i =
        ∑ j, ev (π ≫ p) σ O (c i j) y • valAt f (v j) (hmem y hy) := fun y hy i => by
    have e₁ : spMap (evHom hy) ≫ LogKS.chart ⟨O, hO⟩ = y.1 := spMap_evHom (V := ⟨O, hO⟩) hy
    have e₂ : spMap (evHom hy) ≫ LogKS.chart ⟨O, hO⟩ ≫ π ≫ f = (down π y).1 ≫ f := by
      rw [reassoc_of% e₁]; exact (Category.assoc _ _ _).symm
    have e₃ : (evHom hy).comp (π.appLE V.1 O hle').hom = evHom (hmem y hy) := by
      have : Mono (LogKS.chart V) := by
        have := V.2.isOpenImmersion_fromSpec
        exact inferInstanceAs (Mono (IsAffineOpen.fromSpec V.2))
      have e : spMap ((evHom hy).comp (π.appLE V.1 O hle').hom) = spMap (evHom (hmem y hy)) := by
        rw [← cancel_mono (LogKS.chart V), spMap_evHom, ← spMap_comp_spMap, Category.assoc, hψ, reassoc_of% e₁]
        rfl
      exact congrArg (fun q => q.hom) (Spec.map_injective e)
    have e₄ : coch u y.1 (x := (down π y).1 ≫ f) (Category.assoc _ _ _).symm i =
        LieLocFrame.res (evHom hy) e₂ (coch u (LogKS.chart ⟨O, hO⟩) rfl i) :=
      tan_ext ((congrArg (fun q => raw u q i) e₁.symm).trans (dual_raw u _ _ i).symm)
    rw [e₄, hc i, LieLocFrame.res_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ev_eq hy, LieLocFrame.res_res _ _ _ _ e₃ (by rw [← Category.assoc, spMap_evHom])]
    rfl
  have hGc : ∀ i j, ContinuousOn (fun y => G i j (down π y)) (ptsIn (π ≫ p) σ O) := fun i j => by
    have h₁ := ((hG₁ i j).continuousOn (isOpen_ptsIn _)).comp hd.continuousOn hmem
    have h₂ := ((hG₂ i j).continuousOn (isOpen_ptsIn _)).comp hd.continuousOn hmem
    exact ((Complex.continuous_ofReal.comp_continuousOn h₁).add
      ((Complex.continuous_ofReal.comp_continuousOn h₂).mul continuousOn_const)).congr
        fun y _ => (Complex.re_add_im _).symm
  have hc : ContinuousOn (fun y => ∑ i, ∑ j, star (ev (π ≫ p) σ O (c a i) y) * (G j i (down π y) *
      ev (π ≫ p) σ O (c b j) y)) (ptsIn (π ≫ p) σ O) :=
    continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
      (continuousOn_ev _).star.mul ((hGc j i).mul (continuousOn_ev _))
  refine (hc.congr fun y hy => ?_).continuousAt ((isOpen_ptsIn O).mem_nhds (mem_ptsIn.2 hyO))
  simp only [gramOf, of_apply]
  rw [key y hy a, key y hy b, form_sum]
  simp only [dotProduct, mulVec, Finset.mul_sum, gramOf, of_apply, Pi.star_apply, hG _ _ _ (hmem y hy)]

theorem exists_bound [Finite (k →+* ℂ)] [Mono f] [UniversallyClosed (π ≫ p)] {A : ∀ σ : k →+* ℂ, AnRead p σ d}
    {h : ∀ (σ : k →+* ℂ) (y : CxPts p σ), TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ}
    (hh : ∀ σ, IsLieMetric t f (A σ) (h σ))
    (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback (π ≫ f)).obj t.G) [IsMonHom u]
    (hc : ∀ (K : Type) [Field K] (w : Sp K ⟶ W), IsClosedImmersion ((Over.pullback w).map u).left) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] (w : Sp K ⟶ W) (yK : Sp K ⟶ Z), w ≫ π = yK →
      ∃ ε : Fin r → TanM (yK ≫ f) t.G, IsCochFrame t (yK ≫ f) ε ∧
        ∀ (σ : K →+* ℂ) (σ' : k →+* ℂ) (z : CxPts p σ') (hz : spMap σ ≫ yK ≫ f = z.1 ≫ f),
          ((C : ℂ) • gramOf (h σ' z) (fun i => bcTan σ hz (ε i)) - 1).PosSemidef := by
  have H : ∀ σ' : k →+* ℂ, ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ y : CxPts (π ≫ p) σ',
      ((C : ℂ) • gramOf (h σ' (down π y)) (coch u y.1 (Category.assoc _ _ _).symm) - 1).PosSemidef := fun σ' => by
    have := ProperPoints.compactSpace_pts (pullback.snd (π ≫ p) (spMap σ'))
    have : CompactSpace (CxPts (π ≫ p) σ') :=
      (Points.PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback (π ≫ p) (spMap σ'))).compactSpace
    exact exists_uniform _ (continuous_gram _ π (hh σ') u) fun y =>
      ((hh σ').1 _).gram_posDef (linearIndependent_of_isCochFrame (isCochFrame_coch u _ (hc ℂ y.1)))
  choose C₀ hC₀ using H
  obtain ⟨C, hC⟩ := (Set.finite_range C₀).bddAbove
  refine ⟨C, fun K _ w yK hw => ?_⟩
  subst hw
  refine ⟨coch u w (Category.assoc _ _ _).symm, isCochFrame_coch u _ (hc K w), fun σ σ' z hz => ?_⟩
  have hz' : (spMap σ ≫ w) ≫ π = z.1 := by
    rw [← cancel_mono f, ← hz]
    simp only [Category.assoc]
  obtain ⟨y, hy⟩ : ∃ y : CxPts (π ≫ p) σ', y.1 = spMap σ ≫ w :=
    ⟨⟨spMap σ ≫ w, by rw [← Category.assoc, hz']; exact z.2⟩, rfl⟩
  obtain rfl : down π y = z := Subtype.ext ((congrArg (· ≫ π) hy).trans hz')
  have e : (fun i => bcTan σ hz (coch u w (Category.assoc _ _ _).symm i)) =
      coch u y.1 (Category.assoc _ _ _).symm := funext fun i =>
    tan_ext ((dual_raw u σ w i).trans (congrArg (fun q => raw u q i) hy.symm))
  rw [e]
  exact hC₀ σ' C (hC ⟨σ', rfl⟩) y

end Cont

theorem gram_lower_bound : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (W : Scheme.{0}) (π : W ⟶ gen s.T.Z) (r : ℕ) (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback (π ≫ genι s.T.Z)).obj s.T.Z.t.G), IsFinite π → IsMonHom u → (∀ (k : Type) [Field k] (w : Sp k ⟶ W), IsClosedImmersion ((Over.pullback w).map u).left) → ∃ C : ℝ, ∀ (K : Type) [Field K] (w : Sp K ⟶ W) (yK : Sp K ⟶ gen s.T.Z), w ≫ π = yK → ∃ ε : Fin r → TanM (yK ≫ genι s.T.Z) s.T.Z.t.G, IsCochFrame s.T.Z.t (yK ≫ genι s.T.Z) ε ∧ ∀ (σ : K →+* ℂ) (σ' : κ.c.F →+* ℂ) (z : CxPts (genStr s.T.Z) σ') (hz : spMap σ ≫ yK ≫ genι s.T.Z = z.1 ≫ genι s.T.Z), ((C : ℂ) • gramOf (x.met σ' z) (fun i => bcTan σ hz (ε i)) - 1).PosSemidef := by
  intro D A N j S κ s x W π r u hπ hu hc
  have hpr := isProper_genStr s.T.Z
  have hmono : Mono (genι s.T.Z) := by
    have : Epi (CommRingCat.ofHom (algebraMap (𝓞 κ.c.F) κ.c.F)) :=
      IsLocalization.epi (nonZeroDivisors (𝓞 κ.c.F)) κ.c.F
    have : Mono (spMap (algebraMap (𝓞 κ.c.F) κ.c.F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
    infer_instance
  exact exists_bound (genι s.T.Z) π x.met_smooth u hc

end GlobalTheory.CochGram

end
