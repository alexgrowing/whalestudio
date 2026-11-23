import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqSecHomSecToPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist
open GlobalTheory.ThickeningDetermines (secIdeal)

def ptOf {K : Type} [Field K] {Y : Scheme.{0}} (x : Sp K ⟶ Y) : Y := x (IsLocalRing.closedPoint K)

theorem le_iff_ptOf_mem {K : Type} [Field K] {Y : Scheme.{0}} (x : Sp K ⟶ Y) (U : Y.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ ptOf x ∈ U := le_preimage_iff x U

theorem ptOf_spMap_comp {K K' : Type} [Field K] [Field K'] {Y : Scheme.{0}} (τ : K →+* K') (x : Sp K ⟶ Y) :
    ptOf (spMap τ ≫ x) = ptOf x :=
  congrArg x (Subsingleton.elim (α := PrimeSpectrum K) _ _)

theorem ptOf_comp {K : Type} [Field K] {Y Z : Scheme.{0}} (x : Sp K ⟶ Y) (g : Y ⟶ Z) :
    ptOf (x ≫ g) = g (ptOf x) := rfl

def resPt {Y : Scheme.{0}} (y : Y) : Sp (Y.residueField y) ⟶ Y := Y.fromSpecResidueField y

theorem ptOf_resPt {Y : Scheme.{0}} (y : Y) : ptOf (resPt y) = y := Scheme.fromSpecResidueField_apply _ _

theorem valR_ne_zero_iff {K : Type} [Field K] {Y : Scheme.{0}} (x : Sp K ⟶ Y) {U : Y.Opens} (h : ptOf x ∈ U)
    (f : Γ(Y, U)) : valR x U f ≠ 0 ↔ ptOf x ∈ Y.basicOpen f := by
  rw [← le_iff_ptOf_mem, le_preimage_basicOpen_iff x ((le_iff_ptOf_mem x U).2 h), isUnit_iff_ne_zero]

def cutIdeal {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {ι : Type} (s : ι → L.Sec) : Y.IdealSheafData :=
  ⨆ i, secIdeal hL (s i)

theorem ideal_cutIdeal {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {ι : Type} (s : ι → L.Sec) (W : Y.affineOpens)
    (c : L.ι) (h : W.1 ≤ L.U c) :
    (cutIdeal hL s).ideal W = Ideal.span (Set.range fun i => resG Y h ((s i).f c)) := by
  rw [cutIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply, Ideal.span_range_eq_iSup]
  exact iSup_congr fun i => ideal_secIdeal hL (s i) W c h

theorem mem_support_cutIdeal {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {ι : Type} (s : ι → L.Sec) (y : Y) :
    y ∈ (cutIdeal hL s).support ↔ ∀ i, y ∉ nonzeroLocus (s i) := by
  rw [cutIdeal, Scheme.IdealSheafData.support_iSup]
  simp only [Closeds.mem_iInf]
  refine forall_congr' fun i => ?_
  rw [← SetLike.mem_coe, coe_support_secIdeal]
  rfl

structure LinSys (k : Type) [Field k] where

  Y : Scheme.{0}

  str : Y ⟶ Sp k

  D : ℕ

  L : LB Y

  isLB : L.IsLB

  N : ℕ

  b : Fin N → L.Sec

namespace LinSys

variable {k : Type} [Field k] (S : LinSys k)

instance algebraΓ : Algebra k Γ(S.Y, ⊤) := algebraΓOfHom S.str

structure IsVariety : Prop where

  smooth : SmoothOfRelativeDimension S.D S.str

  proj : IsProjOver S.str

  conn : GeometricallyConnected S.str

  one_le : 1 ≤ S.D

def comb (u : Fin S.N → k) : S.L.Sec := ∑ j, algebraMap k Γ(S.Y, ⊤) (u j) • S.b j

def Indep : Prop := ∀ u, S.comb u = 0 → u = 0

def BasePointFree : Prop := ⨆ j, nonzeroLocus (S.b j) = ⊤

def del : ℤ := topSelfIntersection k S.L S.D

abbrev PtOver {K : Type} [Field K] (φ : k →+* K) : Type := PtsOver S.str (spMap φ)

abbrev Pt (K : Type) [Field K] [Algebra k K] : Type := S.PtOver (algebraMap k K)

def chartAt (y : S.Y) : S.L.ι := (exists_chart S.isLB y).choose

theorem mem_chartAt (y : S.Y) : y ∈ S.L.U (S.chartAt y) := (exists_chart S.isLB y).choose_spec

section Values

variable {K K' : Type} [Field K] [Field K'] (x : Sp K ⟶ S.Y)

def val (s : S.L.Sec) : K := valR x (S.L.U (S.chartAt (ptOf x))) (s.f _)

def powVal {m : ℤ} (s : (lbZPow S.L m).Sec) : K := valR x (S.L.U (S.chartAt (ptOf x))) (zfun s _)

def coords : Fin S.N → K := fun j => S.val x (S.b j)

def baseHom : k →+* K := (Spec.preimage (x ≫ S.str)).hom

theorem comp_str : x ≫ S.str = spMap (S.baseHom x) := (Spec.map_preimage _).symm

variable {S} in

theorem baseHom_ptOver {φ : k →+* K} (x : S.PtOver φ) : S.baseHom x.1 = φ := by
  rw [baseHom, x.2, Spec.preimage_map]; rfl

theorem le_chartAt : ⊤ ≤ x ⁻¹ᵁ S.L.U (S.chartAt (ptOf x)) := (le_iff_ptOf_mem x _).2 (S.mem_chartAt _)

theorem exists_frame_change (i : S.L.ι) (hi : ptOf x ∈ S.L.U i) :
    ∃ c : K, c ≠ 0 ∧ (∀ s : S.L.Sec, valR x (S.L.U i) (s.f i) = c * S.val x s) ∧
      ∀ (m : ℤ) (s : (lbZPow S.L m).Sec), valR x (S.L.U i) (zfun s i) = c ^ m * S.powVal x s := by
  set j := S.chartAt (ptOf x)
  have h : ⊤ ≤ x ⁻¹ᵁ (S.L.U i ⊓ S.L.U j) := (le_iff_ptOf_mem x _).2 ⟨hi, S.mem_chartAt _⟩
  refine ⟨(Units.map (valMap x _ h).hom.toMonoidHom (S.L.g i j)).val, Units.ne_zero _, fun s => ?_, fun m s => ?_⟩
  · rw [← valR_res x inf_le_left h, s.compat i j, valR_mul x _ h, valR_res x inf_le_right h, valR_eq x _ h]
    rfl
  · have e := congrArg (valR x _) (zfun_rel s i j inf_le_left inf_le_right le_rfl)
    rw [valR_mul x _ h, show res le_rfl (S.L.g i j) = S.L.g i j from Units.ext (LB.resG_self _ _)] at e
    refine ((valR_res x inf_le_left h _).symm.trans e).trans (congrArg₂ (· * ·) ?_ (valR_res x inf_le_right h _))
    rw [valR_eq x _ h, ← Units.val_zpow_eq_zpow_val, ← map_zpow]
    rfl

theorem val_ne_zero_iff (s : S.L.Sec) : S.val x s ≠ 0 ↔ ptOf x ∈ nonzeroLocus s :=
  (valR_ne_zero_iff x (S.mem_chartAt _) _).trans (mem_nonzeroLocus_iff_basicOpen s (S.mem_chartAt _)).symm

theorem powVal_ne_zero_iff {m : ℤ} (s : (lbZPow S.L m).Sec) : S.powVal x s ≠ 0 ↔ ptOf x ∈ nonzeroLocus s := by
  refine (valR_ne_zero_iff x (S.mem_chartAt _) _).trans ?_
  rw [basicOpen_zfun]
  exact and_iff_right (S.mem_chartAt _)

theorem val_add (s t : S.L.Sec) : S.val x (s + t) = S.val x s + S.val x t := valR_add x _ (S.le_chartAt x) _ _

theorem val_zero : S.val x 0 = 0 := valR_zero x _ (S.le_chartAt x)

theorem valR_algebraMap (a : k) : valR x ⊤ (algebraMap k Γ(S.Y, ⊤) a) = S.baseHom x a :=
  (valR_comp x S.str ⊤ _).symm.trans (preimage_apply (A := CommRingCat.of k) (x ≫ S.str) a).symm

theorem val_smul (a : k) (s : S.L.Sec) :
    S.val x (algebraMap k Γ(S.Y, ⊤) a • s) = S.baseHom x a * S.val x s :=
  (valR_mul x _ (S.le_chartAt x) _ _).trans (congrArg (· * _)
    ((valR_res x le_top (S.le_chartAt x) _).trans (S.valR_algebraMap x a)))

theorem val_comb (u : Fin S.N → k) : S.val x (S.comb u) = ∑ j, S.baseHom x (u j) * S.coords x j := by
  let e : S.L.Sec →+ K := { toFun := S.val x, map_zero' := S.val_zero x, map_add' := S.val_add x }
  exact (map_sum e _ _).trans (Finset.sum_congr rfl fun j _ => S.val_smul x _ _)

theorem val_spMap_comp (τ : K →+* K') (s : S.L.Sec) : S.val (spMap τ ≫ x) s = τ (S.val x s) := by
  rw [val, ptOf_spMap_comp, valR_spMap_comp τ x _ (S.le_chartAt x), val]

theorem powVal_spMap_comp (τ : K →+* K') {m : ℤ} (s : (lbZPow S.L m).Sec) :
    S.powVal (spMap τ ≫ x) s = τ (S.powVal x s) := by
  rw [powVal, ptOf_spMap_comp, valR_spMap_comp τ x _ (S.le_chartAt x), powVal]

theorem coords_spMap_comp (τ : K →+* K') : S.coords (spMap τ ≫ x) = fun j => τ (S.coords x j) :=
  funext fun _ => S.val_spMap_comp x τ _

variable {S} in

theorem BasePointFree.coords_ne_zero (h : S.BasePointFree) (x : Sp K ⟶ S.Y) : S.coords x ≠ 0 := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (h.ge (Set.mem_univ (ptOf x)))
  exact fun e => (S.val_ne_zero_iff x _).2 hj (congrFun e j)

end Values

def form {d : ℕ} {g : MvPolynomial (Fin S.N) k} (hg : g.IsHomogeneous d) : (lbPow S.L d).Sec :=
  Twist.formSec S.b (mem_polyGrading_natCast.2 hg)

theorem powVal_form {K : Type} [Field K] (x : Sp K ⟶ S.Y) {d : ℕ} {g : MvPolynomial (Fin S.N) k}
    (hg : g.IsHomogeneous d) : S.powVal x (S.form hg) = eval₂ (S.baseHom x) (S.coords x) g := by
  have h := S.le_chartAt x
  rw [powVal, form, zfun_formSec, valR_eq x _ h, chartEval, map_eval₂Hom, coe_eval₂Hom]
  congr 1
  · ext a
    exact ((valR_eq x _ h _).symm.trans (valR_res x le_top h _)).trans (S.valR_algebraMap x a)
  · funext j
    rw [LB.resG_self, ← valR_eq x _ h]
    rfl

def imageIdeal : Ideal (MvPolynomial (Fin S.N) k) :=
  Ideal.span {g | ∃ (d : ℕ) (hg : g.IsHomogeneous d), S.form hg = 0}

theorem mem_imageIdeal_iff {d : ℕ} {g : MvPolynomial (Fin S.N) k} (hg : g.IsHomogeneous d) :
    g ∈ S.imageIdeal ↔ S.form hg = 0 := by
  refine ⟨fun h => zglobal_ext fun i => ?_, fun h => Ideal.subset_span ⟨d, hg, h⟩⟩
  let ψ : MvPolynomial (Fin S.N) k →+* Polynomial Γ(S.Y, S.L.U i) :=
    eval₂Hom (Polynomial.C.comp ((resG S.Y le_top).comp (algebraMap k Γ(S.Y, ⊤))))
      fun j => Polynomial.X * Polynomial.C (resG S.Y le_rfl ((S.b j).f i))
  have key : ∀ {e : ℕ} {p : MvPolynomial (Fin S.N) k} (hp : p.IsHomogeneous e),
      ψ p = Polynomial.X ^ e * Polynomial.C (zfun (S.form hp) i) := fun {e p} hp => by
    rw [form, zfun_formSec, chartEval, map_eval₂Hom, coe_eval₂Hom, coe_eval₂Hom, eval₂_eq, eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : a.degree = e := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← this, Finsupp.degree_apply, mul_left_comm]
  have hle : S.imageIdeal ≤ RingHom.ker ψ := Ideal.span_le.2 (by
    rintro p ⟨e, hp, h0⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, key hp, h0, zfun_zero, map_zero, mul_zero])
  have h1 := hle h
  rw [RingHom.mem_ker, key hg, (Polynomial.monic_X_pow d).mul_right_eq_zero_iff, Polynomial.C_eq_zero] at h1
  exact h1.trans (zfun_zero i).symm

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isHomogeneous_imageIdeal : S.imageIdeal.IsHomogeneous (homogeneousSubmodule (Fin S.N) k) :=
  Ideal.homogeneous_span _ _ fun _ ⟨d, hg, _⟩ => ⟨d, hg⟩

theorem eval₂_coords_eq_zero {K : Type} [Field K] (x : Sp K ⟶ S.Y) {g : MvPolynomial (Fin S.N) k}
    (hg : g ∈ S.imageIdeal) : eval₂ (S.baseHom x) (S.coords x) g = 0 := by
  have hle : S.imageIdeal ≤ RingHom.ker (eval₂Hom (S.baseHom x) (S.coords x)) := Ideal.span_le.2 (by
    rintro p ⟨e, hp, h0⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂Hom, ← S.powVal_form x hp, h0, powVal, zfun_zero]
    exact valR_zero x _ (S.le_chartAt x))
  exact hle hg

def SameImage (y y' : S.Y) : Prop :=
  ∀ (d : ℕ) (g : MvPolynomial (Fin S.N) k) (hg : g.IsHomogeneous d),
    y ∈ nonzeroLocus (S.form hg) ↔ y' ∈ nonzeroLocus (S.form hg)

def Contracts (C : Set S.Y) : Prop := ∀ y ∈ C, ∀ y' ∈ C, S.SameImage y y'

def NoContract (bd : Set S.Y) : Prop :=
  ∀ C : Set S.Y, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 → Disjoint C bd → ¬ S.Contracts C

def ratioField {K : Type} [Field K] (x : Sp K ⟶ S.Y) : Subfield K :=
  Subfield.closure (Set.range (S.baseHom x) ∪ {r | ∃ i j, r = S.coords x i / S.coords x j})

def Birational : Prop := ∃ η : S.Y, IsGenericPoint η Set.univ ∧ S.ratioField (resPt η) = ⊤

def InjOnPts {K : Type} [Field K] [Algebra k K] (P : Set (S.Pt K)) : Prop :=
  ∀ x ∈ P, ∀ x' ∈ P, ∀ c : K, c ≠ 0 → S.coords x'.1 = c • S.coords x.1 → x = x'

theorem sameImage_of_coords {K : Type} [Field K] {φ : k →+* K} (x x' : S.PtOver φ) {c : K} (hc : c ≠ 0)
    (h : S.coords x'.1 = c • S.coords x.1) : S.SameImage (ptOf x.1) (ptOf x'.1) := fun d g hg => by
  have e := eval₂Hom_unit_mul φ (Units.mk0 c hc) (S.coords x.1) (mem_polyGrading_natCast.2 hg)
  rw [← S.powVal_ne_zero_iff, ← S.powVal_ne_zero_iff, powVal_form, powVal_form, baseHom_ptOver, baseHom_ptOver, h]
  exact not_congr ((Units.mul_right_eq_zero (Units.mk0 c hc ^ (d : ℤ))).symm.trans (Eq.congr_left e.symm))

section BaseChange

variable (E : Type) [Field E] [Algebra k E]

def baseChange : LinSys E where
  Y := pullback S.str (spMap (algebraMap k E))
  str := pullback.snd _ _
  D := S.D
  L := S.L.pull (pullback.fst _ _)
  isLB := LB.isLB_pull S.isLB _
  N := S.N
  b j := secPull (S.b j) _

def bcFst : (S.baseChange E).Y ⟶ S.Y := pullback.fst _ _

theorem isPullback_baseChange :
    IsPullback (S.bcFst E) (S.baseChange E).str S.str (spMap (algebraMap k E)) := IsPullback.of_hasPullback _ _

variable {S E} in

def toBase {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra k Ω] [IsScalarTower k E Ω] (x : (S.baseChange E).Pt Ω) :
    S.Pt Ω :=
  ⟨x.1 ≫ S.bcFst E, by
    rw [Category.assoc, (S.isPullback_baseChange E).w, ← Category.assoc, x.2, IsScalarTower.algebraMap_eq k E Ω, ← Spec.map_comp]
    rfl⟩

theorem toBase_bijective (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra k Ω] [IsScalarTower k E Ω] :
    Function.Bijective (toBase : (S.baseChange E).Pt Ω → S.Pt Ω) := by
  refine ⟨fun x x' h => Subtype.ext (pullback.hom_ext (congrArg Subtype.val h) (x.2.trans x'.2.symm)), fun y => ?_⟩
  refine ⟨⟨pullback.lift y.1 (spMap (algebraMap E Ω)) ?_, pullback.lift_snd _ _ _⟩,
    Subtype.ext (pullback.lift_fst _ _ _)⟩
  rw [y.2, IsScalarTower.algebraMap_eq k E Ω, ← Spec.map_comp]
  rfl

theorem exists_coords_baseChange {K : Type} [Field K] (x : Sp K ⟶ (S.baseChange E).Y) :
    ∃ c : K, c ≠ 0 ∧ (S.baseChange E).coords x = c • S.coords (x ≫ S.bcFst E) := by
  have hm := (S.baseChange E).mem_chartAt (ptOf x)
  obtain ⟨c, hc, h, -⟩ := S.exists_frame_change (x ≫ S.bcFst E) ((S.baseChange E).chartAt (ptOf x) PUnit.unit)
    (LB.pull_U_le _ _ hm)
  exact ⟨c, hc, funext fun j => (valR_appLE x _ _ ((S.baseChange E).le_chartAt x) _).trans (h _)⟩

variable {S} in

theorem IsVariety.baseChange (h : S.IsVariety) : (S.baseChange E).IsVariety := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} S.D
  have := h.conn
  exact ⟨MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension S.D) (S.isPullback_baseChange E) h.smooth,
    ProjSpace.isProjOver_pullback_snd _ h.proj,
    inferInstanceAs (GeometricallyConnected (pullback.snd _ _)), h.one_le⟩

variable {S} in

theorem BasePointFree.baseChange (h : S.BasePointFree) : (S.baseChange E).BasePointFree :=
  top_le_iff.1 fun y _ => by
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (h.ge (Set.mem_univ (S.bcFst E y)))
    exact Opens.mem_iSup.2 ⟨j, (nonzeroLocus_secPull (S.b j) _).ge hj⟩

end BaseChange

def cut {ι : Type} (s : ι → Fin S.N → k) : S.Y.IdealSheafData := cutIdeal S.isLB fun i => S.comb (s i)

def IsFiniteSub (I : S.Y.IdealSheafData) : Prop := IsFinite (I.subschemeι ≫ S.str)

structure IsFiniteEtaleSub (I : S.Y.IdealSheafData) : Prop where

  finite : S.IsFiniteSub I

  etale : Etale (I.subschemeι ≫ S.str)

def subPts (I : S.Y.IdealSheafData) (Ω : Type) [Field Ω] [Algebra k Ω] : Set (S.Pt Ω) :=
  {x | ∃ z : Sp Ω ⟶ I.subscheme, z ≫ I.subschemeι = x.1}

theorem mem_subPts_iff (I : S.Y.IdealSheafData) {Ω : Type} [Field Ω] [Algebra k Ω] (x : S.Pt Ω) :
    x ∈ S.subPts I Ω ↔ ptOf x.1 ∈ I.support := by
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := ptOf x.1) trivial
  refine (mem_range_comp_iff_of_isClosedImmersion I.subschemeι hV x.1 ((le_iff_ptOf_mem _ _).2 hx)).trans ?_
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hx, Scheme.mem_zeroLocus_iff]
  refine forall_congr' fun f => ?_
  rw [← valR_ne_zero_iff x.1 hx, not_not, ← RingHom.mem_ker, I.ker_subschemeι_app ⟨V, hV⟩]
  rfl

theorem mem_subPts_cut_iff {ι : Type} (s : ι → Fin S.N → k) {Ω : Type} [Field Ω] [Algebra k Ω] (x : S.Pt Ω) :
    x ∈ S.subPts (S.cut s) Ω ↔ ∀ i, ∑ j, algebraMap k Ω (s i j) * S.coords x.1 j = 0 := by
  rw [mem_subPts_iff, cut, mem_support_cutIdeal]
  refine forall_congr' fun i => ?_
  rw [← val_ne_zero_iff, not_not, val_comb, baseHom_ptOver]

theorem mem_subPts_cut_baseChange_iff (E : Type) [Field E] [Algebra k E] {ι : Type} (s : ι → Fin S.N → E)
    {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra k Ω] [IsScalarTower k E Ω] (x : (S.baseChange E).Pt Ω) :
    x ∈ (S.baseChange E).subPts ((S.baseChange E).cut s) Ω ↔
      ∀ i, ∑ j, algebraMap E Ω (s i j) * S.coords (toBase x).1 j = 0 := by
  obtain ⟨c, hc, h⟩ := S.exists_coords_baseChange E x.1
  refine ((S.baseChange E).mem_subPts_cut_iff s x).trans (forall_congr' fun i => ?_)
  rw [h, ← mul_eq_zero_iff_left hc (b := ∑ j, algebraMap E Ω (s i j) * S.coords (toBase x).1 j), Finset.mul_sum]
  exact Eq.congr_left (Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _)

theorem IsFiniteSub.finite_subPts {S : LinSys k} {I : S.Y.IdealSheafData} (h : S.IsFiniteSub I) (Ω : Type) [Field Ω]
    [Algebra k Ω] : (S.subPts I Ω).Finite := by
  have : IsFinite (I.subschemeι ≫ S.str) := h
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  have : Module.Finite k Γ(I.subscheme, ⊤) :=
    (I.subschemeι ≫ S.str).finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let Z := PtsOver (I.subschemeι ≫ S.str) (spMap (algebraMap k Ω))
  let e : Z → (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := fun z =>
    { (valMap z.1 ⊤ (le_preimage_top _)).hom with
      commutes' := fun a => by
        have h₁ := valR_comp z.1 (I.subschemeι ≫ S.str) ⊤ ((Scheme.ΓSpecIso (.of k)).inv.hom a)
        rw [z.2, valR_specMap (CommRingCat.ofHom (algebraMap k Ω)) a] at h₁
        exact (valR_eq z.1 ⊤ (le_preimage_top _) _).symm.trans h₁.symm }
  have : Finite Z := Finite.of_injective e fun z z' hz => Subtype.ext
    (ext_of_valR (isAffineOpen_top _) (le_preimage_top _) (le_preimage_top _) fun f =>
      (valR_eq _ _ _ f).trans ((congrArg (fun q : _ →ₐ[k] Ω => q f) hz).trans (valR_eq _ _ _ f).symm))
  refine (Set.finite_range (PtsOver.map I.subschemeι rfl _ : Z → S.Pt Ω)).subset ?_
  rintro x ⟨z, hz⟩
  exact ⟨⟨z, by rw [← Category.assoc, hz, x.2]⟩, Subtype.ext hz⟩

end LinSys
end GlobalTheory.Adelic
