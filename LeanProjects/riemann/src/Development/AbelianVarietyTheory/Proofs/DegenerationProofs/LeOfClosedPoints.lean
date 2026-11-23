import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedToIdempotents
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinates
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedChartsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.GradedCharts
open GlobalTheory.ProjSpace GlobalTheory.ZJ Matrix

section General
variable {X Y : Scheme.{0}}

theorem crd_secPull {H : LB X} {J : Type} (s : J → H.Sec) (f : Y ⟶ X) {R : Type} [CommRing R] (x : Sp R ⟶ Y)
    (v : J → R) (h : Crd H s (x ≫ f) v) : Crd (H.pull f) (fun j => GlobalTheory.secPull (s j) f) x v := by
  obtain ⟨l, c, hl, hv⟩ := h
  have h : ⊤ ≤ x ⁻¹ᵁ (H.pull f).U (fun _ => l) := fun z hz => Set.mem_iInter.2 fun _ => hl hz
  refine ⟨fun _ => l, c, h, fun j => ?_⟩
  rw [hv]
  exact congrArg _ (GlobalTheory.Points.valR_appLE x f _ h _).symm

theorem crd_lin {k K : Type} [CommRing k] [CommRing K] {p : X ⟶ Sp k} {H : LB X} {J : Type} [Fintype J]
    {s t : J → H.Sec} {a : Matrix J J k} (ht : ∀ i, IsLin p s (a i) (t i)) {x : Sp K ⟶ X} {ψ : k →+* K}
    (hx : x ≫ p = spMap ψ) {v : J → K} (hv : Crd H s x v) : Crd H t x (a.map ψ *ᵥ v) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  refine ⟨l, c, hl, fun i => ?_⟩
  rw [ht i l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
    GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]
  rfl

theorem isAffineOpen_lin {k : Type} [CommRing k] {p : X ⟶ Sp k} {H : LB X} {J : Type} [Fintype J]
    {s : J → H.Sec} {a : J → k} {φ : H.Sec} (hφ : IsLin p s a φ) (hs : ∀ j, IsAffineOpen (nonzeroLocus (s j))) :
    IsAffineOpen (nonzeroLocus φ) := by
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range fun j => secRatio φ (s j)) ?_ ?_
  · have h : ∑ j, constFn p (nonzeroLocus φ) (a j) * secRatio φ (s j) = 1 := by
      refine (eq_secRatio φ φ fun l => ?_).trans (secRatio_self φ)
      conv_lhs => rw [hφ l]
      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e : ∀ (U V : X.Opens) (e : U ≤ V), resG X e (constFn p V (a j)) = constFn p U (a j) := by
        intro U V e
        unfold constFn
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
        erw [Scheme.Hom.appLE_map]
      rw [map_mul, map_mul, e, e, secRatio_spec φ (s j) l, _root_.mul_assoc]
    rw [Ideal.eq_top_iff_one, ← h]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    rw [basicOpen_secRatio, inf_comm, ← basicOpen_secRatio]
    exact (hs j).basicOpen _

def ofSec {H : LB X} {J Cl : Type} [Finite J] [Finite Cl] (wt : J → Cl) (c₀ : Cl) (s : J → H.Sec)
    (ha : ∀ i, wt i = c₀ → IsAffineOpen (nonzeroLocus (s i)))
    (hc : ⨆ i : {i // wt i = c₀}, nonzeroLocus (s i.1) = ⊤) : Charts X where
  I := J
  Cl := Cl
  wt := wt
  c₀ := c₀
  W i := nonzeroLocus (s i.1)
  aff i := ha i.1 i.2
  cover := hc
  r i j := secRatio (s i.1) (s j)
  r_self _ := secRatio_self _
  inter _ _ := (basicOpen_secRatio _ _).symm
  trans _ _ _ := (secRatio_mul_secRatio _ _ _ _ _).symm

theorem le_of_closedPoints [JacobsonSpace X] {U V : X.Opens}
    (h : ∀ x, IsClosed ({x} : Set X) → x ∈ U → x ∈ V) : U ≤ V := by
  intro x hx
  by_contra hV
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ) ⟨x, hx, hV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  exact hy.2 (h y hc hy.1)

theorem locus_ratio {k : Type} [Field k] [IsAlgClosed k] [IsReduced Y] (π : Y ⟶ Sp k) [LocallyOfFiniteType π]
    (φ : Y ⟶ X) {H : LB X} {H' : LB Y} {J : Type} (s : J → H.Sec) (F : J → H'.Sec)
    (h : ∀ x : Sp k ⟶ Y, x ≫ π = 𝟙 _ → ∃ v, Crd H' F x v ∧ Crd H s (x ≫ φ) v) (i : J) :
    φ ⁻¹ᵁ nonzeroLocus (s i) = nonzeroLocus (F i) ∧ ∀ j, IsRatio (F j) (F i) (φ ⁻¹ᵁ nonzeroLocus (s i))
      ((φ.app (nonzeroLocus (s i))).hom (secRatio (s i) (s j))) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace π
  have key : ∀ y (hc : IsClosed ({y} : Set Y)) (U : Y.Opens), ⊤ ≤ pointOfClosedPoint π y hc ⁻¹ᵁ U ↔ y ∈ U :=
    fun y hc U => (CrdCalc.top_le_iff _ _).trans
      (iff_of_eq (congrArg (· ∈ U) (pointOfClosedPoint_apply π y hc _)))
  have e : φ ⁻¹ᵁ nonzeroLocus (s i) = nonzeroLocus (F i) := by
    have : ∀ y, IsClosed ({y} : Set Y) → (y ∈ φ ⁻¹ᵁ nonzeroLocus (s i) ↔ y ∈ nonzeroLocus (F i)) := by
      intro y hc
      obtain ⟨v, h1, h2⟩ := h _ (pointOfClosedPoint_comp π y hc)
      rw [← key y hc, ← key y hc, ← CrdCalc.crd_isUnit_iff i h1]
      exact (CrdCalc.crd_isUnit_iff i h2).symm
    exact le_antisymm (le_of_closedPoints fun y hc => (this y hc).1) (le_of_closedPoints fun y hc => (this y hc).2)
  refine ⟨e, fun j => ?_⟩
  have e2 : (φ.app (nonzeroLocus (s i))).hom (secRatio (s i) (s j)) = resG Y e.le (secRatio (F i) (F j)) := by
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
    refine le_of_closedPoints fun y hc hy => ?_
    obtain ⟨v, h1, h2⟩ := h _ (pointOfClosedPoint_comp π y hc)
    have hU := (key y hc _).2 (Y.basicOpen_le _ hy)
    have hu := (CrdCalc.isUnit_valR_iff _ _ hU _).2 ((key y hc _).2 hy)
    have hi := (CrdCalc.crd_isUnit_iff i h2).2 hU
    have r1 := CrdCalc.crd_ratio h1 (secRatio_spec (F i) (F j)) ((CrdCalc.crd_isUnit_iff i h1).1 hi)
    have r2 := CrdCalc.crd_ratio h2 (secRatio_spec (s i) (s j)) hU
    rw [CrdCalc.valR_eq _ _ hU, map_sub, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res _ _ hU,
      ← GlobalTheory.Points.valR_comp, hi.mul_right_cancel (r1.symm.trans r2), sub_self] at hu
    exact (not_isUnit_zero hu).elim
  intro l
  rw [e2, GlobalTheory.Cartier.resG_resG]
  exact secRatio_on (F i) (F j) l (inf_le_left.trans e.le) inf_le_right

end General

section Transport
variable {S : Scheme.{0}} {H H' : Over S} [GrpObj H] [GrpObj H'] (e : H ≅ H') [IsMonHom e.hom]
  {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ H')

theorem mul_comp_hom {Y : Over S} (t : Y ⟶ splitTorus S X) (g : Y ⟶ H) :
    ((t ≫ i ≫ e.inv) * g).left ≫ e.hom.left = ((t ≫ i) * (g ≫ e.hom)).left := by
  rw [← Over.comp_left, MonObj.mul_comp, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem hasWt_iff (V : H'.left.Opens) (u : Γ(H'.left, V)) (χ : X) :
    HasWt (i ≫ e.inv) (e.hom.left ⁻¹ᵁ V) ((e.hom.left.app V).hom u) χ ↔ HasWt i V u χ := by
  have c : ∀ {Y : Over S} (a : Y.left ⟶ H.left) (b : Y.left ⟶ H'.left) (_ : a ≫ e.hom.left = b)
      (h : ⊤ ≤ a ⁻¹ᵁ e.hom.left ⁻¹ᵁ V) (h' : ⊤ ≤ b ⁻¹ᵁ V),
      (a.appLE _ ⊤ h).hom ((e.hom.left.app V).hom u) = (b.appLE V ⊤ h').hom u := by
    rintro Y a _ rfl h h'
    rw [Scheme.Hom.comp_appLE]
    rfl
  constructor
  · intro h Y t g k k'
    have e1 : (g ≫ e.inv).left ≫ e.hom.left = g.left := by
      rw [← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    have e2 := mul_comp_hom e i t (g ≫ e.inv)
    rw [Category.assoc, e.inv_hom_id, Category.comp_id] at e2
    have := h Y t (g ≫ e.inv) (e1 ▸ k :  ⊤ ≤ (_ ≫ e.hom.left) ⁻¹ᵁ V) (e2 ▸ k' :  ⊤ ≤ (_ ≫ e.hom.left) ⁻¹ᵁ V)
    exact (c _ _ e2 _ k').symm.trans (this.trans (congrArg _ (c _ _ e1 _ k)))
  · intro h Y t g k k'
    have e2 := mul_comp_hom e i t g
    have k2 : ⊤ ≤ ((t ≫ i) * (g ≫ e.hom)).left ⁻¹ᵁ V := e2 ▸ k'
    rw [c _ (g ≫ e.hom).left rfl _ k, c _ _ e2 _ k2]
    exact h Y t (g ≫ e.hom) k k2

theorem split_pull (C : Charts H'.left) [IsAffineHom e.hom.left] {d : ℕ} {c : Fin d → C.Cl} (h : C.Split c) :
    (C.pull e.hom.left).Split c := by
  obtain ⟨hc, i, hi⟩ := h
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have := hi.hom
  refine ⟨?_, i ≫ e.inv, inferInstance, fun a Y t g k => ?_, fun a j hj => (hasWt_iff e i _ _ _).2 (hi.inv a j hj),
    fun a j k hj => (hasWt_iff e i _ _ _).2 (hi.wt a j k hj), fun k x => ?_, fun a u hu => ?_⟩
  · rw [← Over.w e.hom]
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 S) ⟨(Category.comp_id _).symm⟩) hc
  · have := hi.stable a Y t (g ≫ e.hom) k
    rw [← mul_comp_hom] at this
    exact this
  · obtain ⟨a, j, hj, hx⟩ := hi.bpf k (e.hom.left x)
    exact ⟨a, j, hj, (Scheme.preimage_basicOpen e.hom.left _).le hx⟩
  · obtain ⟨u, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.left.app (C.W a))).2 u
    have h1 := Subring.mem_map.2 ⟨u, hi.gen a u ((hasWt_iff e i _ _ _).1 hu), (rfl : (e.hom.left.app (C.W a)).hom u = _)⟩
    rw [RingHom.map_closure] at h1
    refine Subring.closure_mono ?_ h1
    rintro _ ⟨_, ⟨v, rfl⟩ | ⟨j, hj, rfl⟩, rfl⟩
    · refine Or.inl ⟨v, ?_⟩
      have : ∀ (f : H.left ⟶ S) (_ : e.hom.left ≫ H'.hom = f), f.appLE ⊤ (e.hom.left ⁻¹ᵁ C.W a) le_top =
          H'.hom.appLE ⊤ (C.W a) le_top ≫ e.hom.left.app (C.W a) := by
        rintro _ rfl
        rw [← Scheme.Hom.appLE_eq_app]
        exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
      exact congrArg (fun φ => φ.hom v) (this _ (Over.w e.hom))
    · exact Or.inr ⟨j, hj, rfl⟩

theorem split_pull_of_comp {Z : Scheme.{0}} (C : Charts Z) (h : H.left ⟶ Z) (φ : H'.left ⟶ Z) [IsAffineHom h]
    [IsAffineHom φ] (hφ : e.hom.left ≫ φ = h) {d : ℕ} {c : Fin d → C.Cl} (hs : (C.pull φ).Split c) :
    (C.pull h).Split c := by
  subst hφ
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  exact split_pull e (C.pull φ) hs

end Transport

section Base

theorem eq_of_ne_zero {C J Cl : Type} [Field C] [Fintype J] [DecidableEq J] (e : Cl → Matrix J J C)
    (he : ∀ c c', c ≠ c' → e c * e c' = 0) (b : Matrix J J C) (hb : IsUnit b) (cl : J → Cl)
    (hcl : ∀ j, e (cl j) *ᵥ b j = b j) (a : J → C) (c : Cl) (h : e c *ᵥ (a ᵥ* b) = a ᵥ* b) {j : J} (hj : a j ≠ 0) :
    c = cl j := by
  by_contra hne
  have h1 : ∀ u : J → C, u ᵥ* b = ∑ k, u k • b k := fun u => by
    ext k
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  have h2 : e (cl j) *ᵥ (a ᵥ* b) = 0 := by
    rw [← h, Matrix.mulVec_mulVec, he _ _ (Ne.symm hne), Matrix.zero_mulVec]
  have h3 : (fun k => if cl k = cl j then a k else 0) ᵥ* b = 0 := by
    rw [← h2, h1, h1, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul]
    split_ifs with hk
    · rw [← hk, hcl]
    · rw [← hcl k, Matrix.mulVec_mulVec, he _ _ (Ne.symm hk), Matrix.zero_mulVec, smul_zero, zero_smul]
  have h4 := Matrix.vecMul_injective_of_isUnit hb (h3.trans (Matrix.zero_vecMul b).symm)
  exact hj (by simpa using congrFun h4 j)

theorem exists_immersion {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W) {z : Z} (hz : z ∈ W) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (t : Sp R ⟶ Z) (_ : IsImmersion t),
      t (⊥ : PrimeSpectrum R) = z ∧ ⊤ ≤ t ⁻¹ᵁ W := by
  let q := hW.primeIdealOf ⟨z, hz⟩
  have := q.isPrime
  have : IsClosedImmersion (spMap (Ideal.Quotient.mk q.asIdeal)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨Γ(Z, W) ⧸ q.asIdeal, inferInstance, inferInstance, spMap (Ideal.Quotient.mk _) ≫ hW.fromSpec,
    inferInstance, ?_, GlobalTheory.Points.le_preimage_specMap_fromSpec hW _⟩
  have h : spMap (Ideal.Quotient.mk q.asIdeal) (⊥ : PrimeSpectrum (Γ(Z, W) ⧸ q.asIdeal)) = q :=
    PrimeSpectrum.ext Ideal.mk_ker
  exact (congrArg hW.fromSpec h).trans (hW.fromSpec_primeIdealOf ⟨z, hz⟩)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem proj_mem (hB : BaseFacts S M U₀ EE) (z : M.Z) (c : S.TT M z →+ ZMod S.N) {v : S.J → Ω} (hv : v ∈ EE.E z) :
    (S.proj _ c).map (algebraMap o Ω) *ᵥ v ∈ EE.E z := by
  have := FreeNear.neZero_rN S
  have := Fintype.ofFinite (S.TT M z)
  have hs : ∀ (a : o) (u : S.J → Ω), u ∈ EE.E z → a • u ∈ EE.E z := fun a u hu => by
    rw [← algebraMap_smul (M.O z)]
    exact Submodule.smul_mem _ _ hu
  have e : ∀ (a : o) (A : Matrix S.J S.J o), (a • A).map (algebraMap o Ω) *ᵥ v = a • (A.map (algebraMap o Ω) *ᵥ v) :=
    fun a A => by
      rw [← Matrix.smul_mulVec]
      congr 1
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      exact (Algebra.smul_def _ _).symm
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, e]
  refine hs _ _ ?_
  rw [← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [RingHom.mapMatrix_apply, e]
  exact hs _ _ (hB.stab z _ ((hB.free z).2.le ((hB.free z).1.1 t.2)) v hv)

theorem exists_adapted [hA : ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (z : M.Z) :
    ∃ (W : M.Z.Opens) (l : Q.Λ) (A A' : Matrix S.J S.J Ω) (wt : S.J → (S.TT M z →+ ZMod S.N)),
      IsAffineOpen W ∧ z ∈ W ∧ W ≤ Q.W l ∧ (∀ x ∈ W, S.supI M z ⊆ S.supI M x) ∧
      (∀ x ∈ W, ∀ i j, A i j ∈ M.O x ∧ A' i j ∈ M.O x) ∧ A' * A = 1 ∧
      ∀ i, (S.proj _ (wt i)).map (algebraMap o Ω) *ᵥ (A * Q.B l) i = (A * Q.B l) i := by
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.TT M z)
  have := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := FreeNear.proj_orthogonal S _ (hB.free z).1
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z))
  set P : (S.TT M z →+ ZMod S.N) → Matrix S.J S.J Ω := fun c => (algebraMap o Ω).mapMatrix (S.proj _ c) with hP
  have h : ∀ c i, ∃ a : S.J → M.O z, ∑ j, a j • Q.B l j = P c *ᵥ Q.B l i := fun c i => by
    refine (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun j k => Q.B l j k)).1 ?_
    exact (Q.basis l z hl).le (proj_mem hB z c ((Q.basis l z hl).ge (Submodule.subset_span ⟨i, rfl⟩)))
  choose a ha using h
  let inc := (M.O z).val.toRingHom.mapMatrix (m := S.J)
  have hinc : Function.Injective inc := Matrix.map_injective Subtype.val_injective
  let e : (S.TT M z →+ ZMod S.N) → Matrix S.J S.J (M.O z) := fun c => (Matrix.of (a c))ᵀ
  have he : ∀ c, (Q.B l)ᵀ * inc (e c) = P c * (Q.B l)ᵀ := fun c => by
    ext k i
    have := congrFun (ha c i) k
    simp only [Finset.sum_apply, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul] at this
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans this
  have hu : IsUnit (Q.B l)ᵀ := (Matrix.isUnit_transpose _).2 (IsUnit.of_mul_eq_one_right _ (Q.c_inv l))
  obtain ⟨κ, col, hdet, -⟩ := exists_basis_adapted_to_idempotents (M.O z) S.J _ e
    (fun c c' => hinc (hu.mul_left_cancel (by
      rw [map_mul, ← Matrix.mul_assoc, he, Matrix.mul_assoc, he, ← Matrix.mul_assoc, hP, ← map_mul, hmul]
      split_ifs
      · exact (he c).symm
      · simp)))
    (hinc (hu.mul_left_cancel (by
      rw [map_sum, Matrix.mul_sum, map_one]
      simp only [he]
      rw [← Matrix.sum_mul, hP, ← map_sum, hsum, map_one, Matrix.one_mul, Matrix.mul_one])))
  set A₀ : Matrix S.J S.J (M.O z) := Matrix.of fun i j => e (κ i) j (col i) with hA₀
  let V : M.Z.Opens := ⟨⋂ i, ⋂ j, {x | inc A₀ i j ∈ M.O x} ∩ {x | inc A₀⁻¹ i j ∈ M.O x},
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)⟩
  obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := Q.W l ⊓ ⟨_, OpenPart.isOpen_supI_subset (S := S) z⟩ ⊓ V)
    ⟨⟨hl, fun _ h => h⟩, Set.mem_iInter₂.2 fun i j => ⟨(A₀ i j).2, (A₀⁻¹ i j).2⟩⟩
  refine ⟨W, l, inc A₀, inc A₀⁻¹, κ, hW, hz, fun x hx => (hle hx).1.1, fun x hx => (hle hx).1.2,
    fun x hx i j => Set.mem_iInter₂.1 (hle hx).2 i j, ?_, fun i => ?_⟩
  · rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
  · have e1 : (inc A₀ * Q.B l) i = P (κ i) *ᵥ Q.B l (col i) := by
      rw [← ha]
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      rfl
    rw [e1, Matrix.mulVec_mulVec]
    congr 1
    exact (map_mul (algebraMap o Ω).mapMatrix _ _).symm.trans (congrArg _ ((hmul _ _).trans (if_pos rfl)))

end Base

section Point
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem val_sum_mul {K J : Type} [Field K] [Fintype J] {y : Sp K ⟶ M.Z} {z : M.Z} (h : ∀ w, y w ⤳ z) (a b : J → Ω)
    (ha : ∀ j, a j ∈ M.O z) (hb : ∀ j, b j ∈ M.O z) :
    M.val y (∑ j, a j * b j) = ∑ j, M.val y (a j) * M.val y (b j) := by
  have := map_sum (RatModel.valHomOf y z h) (fun j => ⟨a j, ha j⟩ * ⟨b j, hb j⟩) Finset.univ
  simpa only [map_mul, RatModel.valHomOf_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] using this

theorem mem_G_iff [hA : ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ}
    {A A' : Matrix S.J S.J Ω} (hAA : A' * A = 1) {T : AddSubgroup S.Gam} {wt : S.J → (T →+ ZMod S.N)}
    (hwt : ∀ i, (S.proj _ (wt i)).map (algebraMap o Ω) *ᵥ (A * Q.B l) i = (A * Q.B l) i)
    {K : Type} [Field K] (x : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) {z : M.Z}
    (hz : Set.range (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) = {z}) (hc : IsClosed ({z} : Set M.Z))
    (hT : T = S.TT M z) (hO : ∀ i j, A i j ∈ M.O z ∧ A' i j ∈ M.O z) {w : S.J → K}
    (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x w) :
    ⊤ ≤ (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⁻¹ᵁ Q.G ↔
      ∃ i, wt i = 0 ∧ (A.map (M.val (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom)) *ᵥ w) i ≠ 0 := by
  subst hT
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.TT M z)
  have := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ (hB.free z).1
  have hcrd := Q.rel l _ x _ hw
  have hW : Set.range (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ⊆ Q.W l := by
    rintro _ ⟨q, rfl⟩
    exact (x q).2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : o →+* K, (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ≫ M.s = spMap ψ :=
    ⟨(Spec.preimage ((x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  rw [OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ _ z ψ _ (by rwa [Category.assoc]) (Or.inl hc)
    (by simpa only [Category.assoc] using hψ) hcrd]
  generalize x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t at *
  have hl : z ∈ Q.W l := hW (hz.ge rfl)
  let φ := RatModel.valHom t z hz
  let inc := (algebraMap (M.O z) Ω).mapMatrix (m := S.J)
  have hinc : Function.Injective inc := Matrix.map_injective Subtype.val_injective
  let C : Matrix S.J S.J (M.O z) := fun i j => ⟨_, RatModel.valF_mem_O hl (Q.c l i j)⟩
  let a : Matrix S.J S.J (M.O z) := fun i j => ⟨_, (hO i j).1⟩
  let a' : Matrix S.J S.J (M.O z) := fun i j => ⟨_, (hO i j).2⟩
  have haa : a' * a = 1 := hinc (by rw [map_mul, map_one]; exact hAA)
  set P : Matrix S.J S.J Ω := (S.proj (S.TT M z) 0).map (algebraMap o Ω) with hP
  have hE : EE.E z = Submodule.span (M.O z) (Set.range (A * Q.B l)) := by
    have key : ∀ (u : Matrix S.J S.J (M.O z)) (b : Matrix S.J S.J Ω),
        Submodule.span (M.O z) (Set.range (inc u * b)) ≤ Submodule.span (M.O z) (Set.range b) := fun u b => by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun j k => b j k)).2 ⟨u i, funext fun k => ?_⟩
      rw [Finset.sum_apply]
      rfl
    refine (Q.basis l z hl).trans (le_antisymm ?_ (key a _))
    have := key a' (A * Q.B l)
    rwa [← Matrix.mul_assoc, show inc a' * A = 1 from hAA, Matrix.one_mul] at this
  have := TestCrit.exists_ne_zero_iff Subtype.val_injective φ (C * a')
    (fun i j => algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) (A * Q.B l) ?_ {i | wt i = 0} ?_ (a.map φ *ᵥ w)
  · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_assoc, haa, Matrix.mul_one] at this
    have e1 : (Q.c l).map (valR t (Q.W l)) = C.map φ := by
      ext i j
      exact (RatModel.val_valF hW _).symm
    have e2 : ∀ u : o, ψ u = φ (algebraMap o (M.O z) u) := fun u => (RatModel.val_algebraMap hψ u).symm
    simp only [e1, e2]
    exact this
  · rw [Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ A, show a'.map (algebraMap (M.O z) Ω) * A = 1 from hAA,
      Matrix.one_mul]
    exact Q.c_inv l
  · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, hi, rfl⟩
      have h0 := hwt i
      rw [show wt i = 0 from hi] at h0
      have h1 := hB.zero z hc _ (hE.ge (Submodule.subset_span ⟨i, rfl⟩)) h0
      refine (Submodule.mem_span_range_iff_exists_fun (M.O z)).2 ⟨fun j => ⟨_, h1 j⟩, funext fun k => ?_⟩
      rw [Finset.sum_apply]
      exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans (congrFun h0 k)
    · rintro _ ⟨i, rfl⟩
      obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun j k => (A * Q.B l) j k)).1
        (hE.le (hB.mem z i))
      have h1 : (fun j => algebraMap (M.O z) Ω (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i))) =
          P *ᵥ Pi.single i 1 := by
        rw [Matrix.mulVec_single_one]
        rfl
      change (fun j => algebraMap (M.O z) Ω (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i))) ∈ _
      rw [h1, ← hu, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      refine Submodule.smul_mem _ _ ?_
      change P *ᵥ (A * Q.B l) j ∈ _
      by_cases hj : wt j = 0
      · have h0 := hwt j
        rw [hj] at h0
        rw [h0]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      · rw [← hwt j, Matrix.mulVec_mulVec, hP, ← Matrix.map_mul, hmul, if_neg (Ne.symm hj), Matrix.map_zero _ (map_zero _),
          Matrix.zero_mulVec]
        exact Submodule.zero_mem _

theorem exists_matrix [hA : ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ}
    {A A' : Matrix S.J S.J Ω} (hAA : A' * A = 1) {T : AddSubgroup S.Gam} {wt : S.J → (T →+ ZMod S.N)}
    (hwt : ∀ i, (S.proj _ (wt i)).map (algebraMap o Ω) *ᵥ (A * Q.B l) i = (A * Q.B l) i)
    {p : ℕ} [Fact p.Prime] {y : Sp (ZH.OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u)
    (tm : Q.TMap t c) (hU : Set.range (ZH.gPt p ≫ y) ⊆ U₀) (hl : y (ZH.cPt p) ∈ Q.W l)
    (hT : T = S.TT M (y (ZH.cPt p))) (hO : ∀ i j, A i j ∈ M.O (y (ZH.cPt p)) ∧ A' i j ∈ M.O (y (ZH.cPt p))) :
    ∃ (m : Matrix S.J S.J (ZH.kb p)) (cl : t.u.D.toPre.X → (T →+ ZMod S.N)), IsUnit m.det ∧
      (∀ α β, cl α = cl β ↔ ∃ n, α = β + S.N • n) ∧ cl 0 = 0 ∧ (∀ i j, m i j ≠ 0 → wt i = cl (t.cls j)) ∧
      ∀ (x : Sp (ZH.kb p) ⟶ t.mod.Φ.G.left) (x' : Sp (ZH.kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (v w : S.J → ZH.kb p),
        x ≫ t.mod.Φ.G.hom = 𝟙 _ →
        x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι →
        Crd (t.mod.Φ.H 1) t.mod.F x v → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w →
        ∃ u : (ZH.kb p)ˣ, A.map (M.val (ZH.rPt p ≫ y)) *ᵥ w = fun j => (u : ZH.kb p) * (m *ᵥ v) j := by
  have : IsDomain o := hA.inj.isDomain
  obtain ⟨ψ, hψ⟩ : ∃ ψ : o →+* ZH.OO p, y ≫ M.s = spMap ψ :=
    ⟨(Spec.preimage (y ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hg : (ZH.gPt p ≫ y) ≫ M.s = spMap ((ZH.OO p).subtype.comp ψ) := by
    rw [Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hy₀ : ∀ a : o, y₀ (algebraMap o S.R a) = (ψ a : PadicAlgCl p) := fun a =>
    (c.at_ _).trans (RatModel.val_algebraMap hg a)
  obtain ⟨hker, hcl, -⟩ := GlobalTheory.T.span_rows_classZero_eq_invariant o Ω S ρ p y₀ t fun a => by
    rw [hy₀]
    exact (mem_OO_iff _).1 (ψ a).2
  obtain rfl : T = S.perp t.l.yy.ker := by
    rw [hT, ThetaSys.TT, hB.atTest _ p y y₀ t.τ ⟨rfl, hU⟩ c.at_, hker]
  have := FreeNear.finite_char S (S.perp t.l.yy.ker)
  have := Fintype.ofFinite (S.perp t.l.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ t.l.isoFree
  obtain ⟨g, hg1, hg2⟩ := InFibChart.exists_change Q tm.l l tm.mem hl
  obtain ⟨g', hg1', -⟩ := InFibChart.exists_change Q l tm.l hl tm.mem
  let inc := (algebraMap (M.O (y (ZH.cPt p))) Ω).mapMatrix (m := S.J)
  have hinc : Function.Injective inc := Matrix.map_injective Subtype.val_injective
  let a : Matrix S.J S.J (M.O (y (ZH.cPt p))) := fun i j => ⟨_, (hO i j).1⟩
  let a' : Matrix S.J S.J (M.O (y (ZH.cPt p))) := fun i j => ⟨_, (hO i j).2⟩
  have ha : IsUnit a := IsUnit.of_mul_eq_one_right a' (hinc (by rw [map_mul, map_one]; exact hAA))
  have hgu : IsUnit g := IsUnit.of_mul_eq_one g' (hinc ((IsUnit.of_mul_eq_one_right _ (Q.c_inv l)).mul_right_cancel (by
    rw [map_mul, map_one, Matrix.mul_assoc, Matrix.one_mul]
    exact (congrArg (inc g * ·) hg1'.symm).trans hg1.symm)))
  let φ := RatModel.valLoc y (y (ZH.cPt p)) specializes_rfl
  let n : Matrix S.J S.J (ZH.OO p) := (a * g).map φ * tm.m.map t.u.j
  have hn : IsUnit n := ((ha.mul hgu).map φ.mapMatrix).mul
    (((Matrix.isUnit_iff_isUnit_det _).2 tm.unit).map t.u.j.mapMatrix)
  refine ⟨n.map (IsLocalRing.residue _), t.l.wt,
    (Matrix.isUnit_iff_isUnit_det _).1 (hn.map (IsLocalRing.residue _).mapMatrix), hcl, map_zero _,
    fun i j hij => ?_, fun x x' v w hx hx' hv hw => ?_⟩
  · set ξ := (ZH.gPt p ≫ y) (IsLocalRing.closedPoint _) with hξ
    have hr := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (ZH.gPt p ≫ y) (IsLocalRing.closedPoint _))
    have hsp : ξ ⤳ y (ZH.cPt p) := RatModel.gPt_specializes rfl _
    have hBm : ∀ i j, Q.B tm.l i j ∈ M.O ξ := fun i => by
      have h1 : Q.B tm.l i ∈ EE.E ξ := by
        rw [Q.basis _ _ (hsp.mem_open (Q.W tm.l).isOpen tm.mem)]
        exact Submodule.subset_span ⟨i, rfl⟩
      rw [hB.ee.1 ξ (hU ⟨_, rfl⟩)] at h1
      exact (RatModel.Lat.mem_const_iff M).1 h1
    have hb : IsUnit (t.b.map (algebraMap _ (PadicAlgCl p))) := by
      have h1 : ((Q.c tm.l).map (valF M.pt (Q.W tm.l))).map (M.val (ZH.gPt p ≫ y)) *
          (Q.B tm.l).map (M.val (ZH.gPt p ≫ y)) = 1 := by
        rw [← Matrix.map_one (M.val (ZH.gPt p ≫ y)) (RatModel.val_zero _) (RatModel.val_one _), ← Q.c_inv tm.l]
        ext i j
        exact (val_sum_mul hr _ _ (fun k => RatModel.O_le_of_specializes hsp (RatModel.valF_mem_O tm.mem _))
          fun k => hBm k j).symm
      rw [tm.m_eq, ← Matrix.mul_assoc] at h1
      exact IsUnit.of_mul_eq_one_right _ h1
    have e1 : A * Q.B l = inc (a * g) * Q.B tm.l := by
      rw [map_mul, Matrix.mul_assoc]
      exact congrArg (A * ·) hg1
    have hm : ∀ k, (A * Q.B l) i k ∈ M.O ξ := fun k => by
      rw [e1]
      exact sum_mem fun j _ => mul_mem (RatModel.O_le_of_specializes hsp ((a * g) i j).2) (hBm j k)
    have e2 : (n.map (ZH.OO p).subtype) i ᵥ* t.b.map (algebraMap _ (PadicAlgCl p)) =
        fun k => M.val (ZH.gPt p ≫ y) ((A * Q.B l) i k) := by
      funext k
      change (n.map (ZH.OO p).subtype * t.b.map (algebraMap _ (PadicAlgCl p))) i k = _
      rw [Matrix.map_mul, Matrix.mul_assoc, e1]
      refine (congrArg (fun q => (((a * g).map φ).map (ZH.OO p).subtype * q) i k) tm.m_eq.symm).trans ?_
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (val_sum_mul hr _ _
        (fun j => RatModel.O_le_of_specializes hsp ((a * g) i j).2) fun j => hBm j k).symm
      exact congrArg (· * _) (RatModel.val_gPt rfl ((a * g) i j)).symm
    refine eq_of_ne_zero (fun c => (S.proj _ c).map (y₀.comp (algebraMap o S.R))) (fun c c' h => ?_) _ hb
      (fun j => t.l.wt (t.cls j)) t.wt ((n.map (ZH.OO p).subtype) i) (wt i) ?_ (j := j) fun h0 => hij ?_
    · rw [← Matrix.map_mul, hmul, if_neg h, Matrix.map_zero _ (map_zero _)]
    · rw [e2]
      funext k
      refine Eq.trans ?_ (congrArg (M.val (ZH.gPt p ≫ y)) (congrFun (hwt i) k))
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (val_sum_mul hr _ _
        (fun j => Subalgebra.algebraMap_mem _ _) hm).symm
      exact congrArg (· * _) (c.at_ _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext h0 : n i j = 0)).trans (map_zero _)
  · have h1 : (x ≫ t.mod.r) ≫ t.u.G.hom = spMap ((IsLocalRing.residue _).comp t.u.j) := by
      rw [Category.assoc, t.mod.cart.1.w, ← Category.assoc, hx, Category.id_comp, ← Spec.map_comp]
      rfl
    have h2 := tm.crd _ _ _ v h1 (t.mod.red (Over.homMk x hx) v hv)
    have h3 : ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = ZH.rPt p ≫ y := by
      rw [Category.assoc, tm.f_over, ← Category.assoc, h1]
      refine Eq.trans ?_ (congrArg (ZH.rPt p ≫ ·) c.fac)
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    obtain ⟨u, hu⟩ := InFibChart.crd_change Q hB.ov.ne tm.l l _ x' _ (by simpa only [Category.assoc] using hx') h3
      (congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZH.OO p)))) tm.mem hl g hg2 h2 hw
    obtain ⟨i, hi⟩ := GlobalTheory.Points.exists_le_preimage_of_iSup_eq_top x'
      (show ⨆ i, nonzeroLocus (Q.σ l i) = ⊤ by simpa using (Q.imm l).1)
    have h4 := ((CrdCalc.crd_isUnit_iff i hw).2 hi).ne_zero
    rw [hu] at h4
    refine ⟨Units.mk0 u (left_ne_zero_of_mul h4), ?_⟩
    have e : ∀ q : Matrix S.J S.J (M.O (y (ZH.cPt p))), (q.map φ).map (IsLocalRing.residue _) =
        q.map fun a => M.val (ZH.rPt p ≫ y) a := fun q => by
      funext i j
      exact (RatModel.val_spMap_comp (IsLocalRing.residue (ZH.OO p)) y specializes_rfl (q i j)).symm
    rw [hu, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, e, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact Matrix.mulVec_smul _ u _

end Point

section Main
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_sections [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ}
    {A A' : Matrix S.J S.J Ω} (hAA : A' * A = 1) {T : AddSubgroup S.Gam} {wt : S.J → (T →+ ZMod S.N)}
    (hwt : ∀ i, (S.proj _ (wt i)).map (algebraMap o Ω) *ᵥ (A * Q.B l) i = (A * Q.B l) i)
    {W : M.Z.Opens} (hne : (W : Set M.Z).Nonempty) (hle : W ≤ Q.W l)
    (hO : ∀ x ∈ W, ∀ i j, A i j ∈ M.O x ∧ A' i j ∈ M.O x) {R : Type} [CommRing R] (t : Sp R ⟶ M.Z)
    [LocallyOfFiniteType t] (htW : ⊤ ≤ t ⁻¹ᵁ W) (hT : ∀ q, T = S.TT M (t q)) :
    ∃ (H : LB (pullback (Q.G.ι ≫ Q.P.hom) t)) (s : S.J → H.Sec),
      (∀ i, wt i = 0 → IsAffineOpen (nonzeroLocus (s i))) ∧ ⨆ i : {i // wt i = 0}, nonzeroLocus (s i.1) = ⊤ ∧
      ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback (Q.G.ι ≫ Q.P.hom) t),
        ∃ x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x ≫ pullback.fst _ _ ≫ Q.G.ι ∧
          ∀ w, Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w →
            Crd H s x (A.map (M.val (x ≫ pullback.snd _ _ ≫ t)) *ᵥ w) := by
  have := M.sep
  have := Q.proper
  have := hB.jac
  have : IsAffineHom t := IsAffineHom.of_comp t M.s
  choose a ha using fun i j => (RatModel.mem_ringOn_iff_exists hne).1
    (RatModel.mem_ringOn.2 fun x hx => (hO x hx i j).1)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : pullback Q.P.hom t ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme,
      ξ ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = pullback.fst _ _ :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q x ∈ Q.W l) (pullback.condition (f := Q.P.hom) (g := t))).mpr
        (hle (htW (Set.mem_univ (pullback.snd Q.P.hom t x))))), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsAffineHom (ξ ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) := by
    rw [hξ]
    exact isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsAffineHom ξ := IsAffineHom.of_comp ξ (Q.P.hom ⁻¹ᵁ Q.W l).ι
  choose s hs using fun i => (GlobalTheory.SecRatio.existsUnique_isLin (pullback.snd Q.P.hom t)
    (fun j => GlobalTheory.secPull (Q.σ l j) ξ) fun j => valR t W (a i j)).exists
  have haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)) := fun i => isAffineOpen_lin (hs i) fun j => by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact ((Q.imm l).2 j trivial).1.preimage ξ
  have hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback Q.P.hom t) (w : S.J → K),
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) (x ≫ ξ) w →
      Crd _ s x (A.map (M.val (x ≫ pullback.snd _ _ ≫ t)) *ᵥ w) := fun K _ x w hw => by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : R →+* K, x ≫ pullback.snd Q.P.hom t = spMap ψ :=
      ⟨(Spec.preimage (x ≫ pullback.snd Q.P.hom t)).hom, (Spec.map_preimage _).symm⟩
    have h1 := crd_lin (a := Matrix.of fun i j => valR t W (a i j)) hs hψ (crd_secPull _ ξ x w hw)
    obtain ⟨h2, h3⟩ := CrdCalc.valR_spMap ψ t W htW
    have e : A.map (M.val (spMap ψ ≫ t)) = (Matrix.of fun i j => valR t W (a i j)).map ψ := by
      funext i j
      exact (RatModel.val_eq ((top_le_preimage_iff _ _).1 h2) (ha i j)).trans (h3 _)
    rwa [← Category.assoc, hψ, e]
  have : JacobsonSpace (pullback Q.P.hom t : Scheme.{0}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd Q.P.hom t ≫ t)
  have hcrit : ∀ q : (pullback Q.P.hom t : Scheme.{0}), IsClosed ({q} : Set (pullback Q.P.hom t : Scheme.{0})) →
      (q ∈ pullback.fst Q.P.hom t ⁻¹ᵁ Q.G ↔ ∃ i, wt i = 0 ∧ q ∈ nonzeroLocus (s i)) := fun q hq => by
    let x : Sp ((pullback Q.P.hom t).residueField q) ⟶ pullback Q.P.hom t := (pullback Q.P.hom t).fromSpecResidueField q
    have hx : ∀ U : (pullback Q.P.hom t).Opens, ⊤ ≤ x ⁻¹ᵁ U ↔ q ∈ U := fun U =>
      (CrdCalc.top_le_iff x U).trans (iff_of_eq (congrArg (· ∈ U) (Scheme.fromSpecResidueField_apply q _)))
    have e : (x ≫ ξ) ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x ≫ pullback.snd _ _ ≫ t := by
      rw [Category.assoc, reassoc_of% hξ, pullback.condition]
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) (x ≫ ξ)
    have h1 := mem_G_iff hB Q hAA hwt (x ≫ ξ) (z := t (pullback.snd Q.P.hom t q)) (by
        rw [e, RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
        exact congrArg (fun u => ({t (pullback.snd Q.P.hom t u)} : Set M.Z)) (Scheme.fromSpecResidueField_apply q _))
      ((pullback.snd Q.P.hom t ≫ t).closePoints_subset_preimage_closedPoints hq) (hT _)
      (hO _ (htW (Set.mem_univ _))) hw
    rw [Category.assoc, hξ, e] at h1
    refine (hx _).symm.trans (h1.trans (exists_congr fun i => and_congr_right fun _ => ?_))
    exact isUnit_iff_ne_zero.symm.trans ((CrdCalc.crd_isUnit_iff i (hcrd _ x w hw)).trans (hx _))
  let κ : pullback (Q.G.ι ≫ Q.P.hom) t ⟶ pullback Q.P.hom t :=
    pullback.map _ _ _ _ Q.G.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have h1 : κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Q.G.ι := pullback.lift_fst _ _ _
  have h2 : κ ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine ⟨_, fun i => GlobalTheory.secPull (s i) κ, fun i hi => ?_, ?_, fun K _ x => ⟨(x ≫ κ) ≫ ξ, ?_, fun w hw => ?_⟩⟩
  · rw [GlobalTheory.nonzeroLocus_secPull]
    refine (haff i).preimage_of_isOpenImmersion κ
      ((le_of_closedPoints fun q hq h => (hcrit q hq).2 ⟨i, hi, h⟩).trans fun q hq => ?_)
    change q ∈ Set.range κ
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨⟨_, hq⟩, rfl⟩, ⟨_, rfl⟩⟩
  · simp only [GlobalTheory.nonzeroLocus_secPull, ← Scheme.Hom.preimage_iSup]
    have h3 : pullback.fst Q.P.hom t ⁻¹ᵁ Q.G ≤ ⨆ i : {i // wt i = 0}, nonzeroLocus (s i.1) :=
      le_of_closedPoints fun q hq h => by
        obtain ⟨i, hi, h⟩ := (hcrit q hq).1 h
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, h⟩
    refine top_le_iff.1 fun q _ => h3 ?_
    exact (congrArg (fun f => f q ∈ Q.G) h1).mpr (pullback.fst (Q.G.ι ≫ Q.P.hom) t q).2
  · rw [Category.assoc, hξ, Category.assoc, h1]
  · have h3 := hcrd K (x ≫ κ) w hw
    rw [Category.assoc, reassoc_of% h2] at h3
    exact crd_secPull s κ x _ h3

theorem exists_hom {V C : Type} [CommRing V] [IsDomain V] [Field C] (g : V →+* C) (hg : Function.Injective g) :
    ∃ φ : FractionRing V →+* C, spMap g = spMap φ ≫ jK V := by
  refine ⟨IsFractionRing.lift hg, ?_⟩
  have h : (IsFractionRing.lift hg).comp (algebraMap V (FractionRing V)) = g :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a
  exact (congrArg (fun f => spMap f) h.symm).trans (Spec.map_comp
      (CommRingCat.ofHom (algebraMap V (FractionRing V))) (CommRingCat.ofHom (IsFractionRing.lift hg)))

theorem cl_of_test {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) : C.Cl y := by
  obtain ⟨φ, hφ⟩ := exists_hom ((ZJ.OO p).subtype.comp τ.j) (Subtype.val_injective.comp τ.j_inj)
  have e₀ : ZJ.gPt p ≫ spMap τ.j = spMap φ ≫ jK τ.V := by
    rw [← hφ, ← Spec.map_comp]
    rfl
  have e : ZJ.gPt p ≫ y = (spMap φ ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← reassoc_of% e₀, τ.fac]
  unfold Core.Cl
  rw [e]
  rintro _ ⟨a, rfl⟩
  exact ((spMap φ ≫ τ.yK) a).2

end Main

end GlobalTheory.ZH.GradedCharts
end
