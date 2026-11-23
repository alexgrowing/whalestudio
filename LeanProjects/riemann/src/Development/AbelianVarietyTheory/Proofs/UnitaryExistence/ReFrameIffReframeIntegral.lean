import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneralizedScalarsNumberField

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReframeClauses

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.GeneralizedScalarsNumberField
open Formalism.L2.PjFree (FrBaseChg ReFrame XoNumPt TanLin SClause IntRebase)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem isPullback_dualMap (f : R →+* R') :
    IsPullback (spMap (dualMap f)) (spMap (algebraMap R' (DualNumber R'))) (spMap (algebraMap R (DualNumber R)))
      (spMap f) := by
  have w := ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_alg f
  have dec : ∀ {A : Type} [CommRing A] (x : DualNumber A),
      x = algebraMap A (DualNumber A) x.fst + algebraMap A (DualNumber A) x.snd * DualNumber.eps := fun x => by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have he : dualMap f DualNumber.eps = DualNumber.eps := by
    ext <;> simp [dualMap]
  refine isPullback_SpecMap_of_isPushout (CommRingCat.ofHom (algebraMap R (DualNumber R))) (CommRingCat.ofHom f)
    (CommRingCat.ofHom (dualMap f)) (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ?_
  refine ⟨⟨congrArg CommRingCat.ofHom w⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)⟩⟩
  · letI := s.inr.hom.toAlgebra
    exact CommRingCat.ofHom (DualNumber.lift (R := R') (A := R') ⟨(Algebra.ofId R' s.pt, s.inl.hom DualNumber.eps),
      by rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ => Commute.all _ _⟩).toRingHom
  · have hs : ∀ x, s.inl.hom (algebraMap R (DualNumber R) x) = s.inr.hom (f x) := fun x =>
      RingHom.congr_fun (congrArg CommRingCat.Hom.hom s.condition) x
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    conv_rhs => rw [dec x, map_add, map_mul, hs, hs]
    simp [DualNumber.lift_apply_apply, dualMap]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp
    rfl
  · have e₁ : m.hom DualNumber.eps = s.inl.hom DualNumber.eps := by
      rw [← h₁, ← he]; rfl
    have e₂ : ∀ x, m.hom (algebraMap R' (DualNumber R') x) = s.inr.hom x := fun x => by rw [← h₂]; rfl
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    conv_lhs => rw [dec x, map_add, map_mul, e₁, e₂, e₂]
    simp [DualNumber.lift_apply_apply]
    rfl

theorem epi_dualMap {f : R →+* R'} (hf : f.FaithfullyFlat) : Epi (spMap (dualMap f)) := by
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).2 hf
  have : Flat (spMap (dualMap f)) := MorphismProperty.of_isPullback (P := @Flat) (isPullback_dualMap f).flip h1
  have : Surjective (spMap (dualMap f)) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_dualMap f).flip h2
  exact Flat.epi_of_flat_of_surjective _

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Comb

variable {S S' : Type} [CommRing S] [CommRing S']

theorem isCombAt_bc (φ : S →+* S') {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) :
    IsCombAt (spMap φ ≫ x) (fun j => spMap (dualMap φ) ≫ v j) (fun j => φ (a j)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let p : tEps (spMap φ ≫ x) ⟶ tEps x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, (isPullback_dualMap φ).w, Category.assoc])
  refine ⟨fun j => p ≫ u j, fun j => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u j).left = _
    rw [hu j, ← Category.assoc, ← Category.assoc, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp',
      ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_pre_prod]
    rfl

theorem isTanAt_of_isCombAt {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsTanAt x w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_tan x _ (fun j => hv j) a

theorem isEigAt_of_isCombAt [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {τ : E →+* ℂ}
    (he : ∀ j, IsEigAt c τ (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsEigAt c τ w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_eig x c τ (fun j => ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_lt x (v j) (hv j)) he a

end Comb

section Gen

variable {S : Type} [CommRing S] [Algebra c.F S]

theorem id_appLE_apply (X : Scheme.{0}) (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (r : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom r = r := by
  have : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]; rfl

theorem same_point_of_sClause {a : S} {y y' : FrPt Xo c S} (h : SClause a y y') : y'.x = y.x := by
  obtain ⟨pm, h1, h2, -⟩ := h
  have w : ∀ x : Sp S ⟶ Xo.X, (fst (Over.mk x) Xo.univ.t.G).left ≫ x =
      (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom := fun x =>
    (Over.w (fst (Over.mk x) Xo.univ.t.G)).trans (Over.w (snd (Over.mk x) Xo.univ.t.G)).symm
  have e : (fst (Over.mk y'.x) Xo.univ.t.G).left ≫ y'.x = (fst (Over.mk y'.x) Xo.univ.t.G).left ≫ y.x := by
    rw [w y'.x, ← h1, ← h2, Category.assoc, Category.assoc, w y.x]
  have s : (lift (𝟙 (Over.mk y'.x)) (1 : Over.mk y'.x ⟶ Xo.univ.t.G)).left ≫
      (fst (Over.mk y'.x) Xo.univ.t.G).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  have := congrArg (fun q => (lift (𝟙 (Over.mk y'.x)) (1 : Over.mk y'.x ⟶ Xo.univ.t.G)).left ≫ q) e
  simp only [← Category.assoc, s] at this
  exact (Category.id_comp _).symm.trans (this.trans (Category.id_comp _))

theorem sClause_iff (a : S) (y y' : FrPt Xo c S) : SClause a y y' ↔ GenScal a y y' := by
  constructor
  · intro h
    have hx := same_point_of_sClause h
    obtain ⟨x', o', u, ht, he, hb, s, hs⟩ := y'
    simp only at hx
    subst hx
    obtain ⟨pm, h1, h2, h3⟩ := h
    have hp : pm = 𝟙 _ := by
      apply pullback.hom_ext
      · exact h2.trans (Category.id_comp _).symm
      · exact h1.trans (Category.id_comp _).symm
    subst hp
    exact ⟨rfl, fun i => (h3 i le_rfl).symm.trans (id_appLE_apply _ _ _ _)⟩
  · rintro ⟨hx, h⟩
    obtain ⟨x', o', u, ht, he, hb, s, hs⟩ := y'
    simp only at hx
    subst hx
    exact ⟨𝟙 _, Category.id_comp _, Category.id_comp _, fun i hi => (id_appLE_apply _ _ hi _).trans (h i).symm⟩

theorem isUnit_of_genScal {a : S} {y y' : FrPt Xo c S} (h : GenScal a y y') : IsUnit a := by
  obtain ⟨hx, h⟩ := h
  obtain ⟨x', o', u, ht, he, hb, s, hs⟩ := y'
  simp only at hx
  subst hx
  obtain ⟨b, hb', -⟩ := hs y.s
  have h1 : ∀ i, y.s.f i = scal y.x (b * a) i * y.s.f i := fun i => by
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_scal_mul, _root_.mul_assoc]
    exact (hb' i).trans (congrArg _ (h i))
  have h2 : ∀ i, y.s.f i = scal y.x 1 i * y.s.f i := fun i => by
    simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_one, _root_.one_mul]
  exact IsUnit.of_mul_eq_one_right b ((y.gen y.s).unique h1 h2)

end Gen

variable (Xo c)

theorem frBaseChg_iff : FrBaseChg Xo c ↔ BaseChangeField Xo c :=
  ⟨fun h S T _ _ _ _ => h S T, fun h S T _ _ _ _ => h S T⟩

theorem reFrame_iff : ReFrame Xo c ↔ ReframeIntFr Xo c :=
  ⟨fun h T io y => h T io y, fun h T io y => h T io y⟩

theorem reFrame_iff_reframeIntegral (hS : SpreadSt Xo c) : ReFrame Xo c ↔ ReframeIntegral Xo c := by
  constructor
  · intro h T io
    let _ := io.toAlgebra
    intro y y' hy hx
    obtain ⟨t, z, hz⟩ := h T io ⟨y, hS _ y, hy⟩ y' hx
    exact ⟨t, z.1, hz, z.2.2⟩
  · intro h T io
    let _ := io.toAlgebra
    intro y y' hx
    obtain ⟨t, z, hz, hi⟩ := h T io y.1 y' y.2.2 hx
    exact ⟨t, ⟨z, hS _ z, hi⟩, hz⟩

theorem xoNumPt_iff : XoNumPt Xo c ↔ PointNumberField Xo c := by
  constructor
  · rintro ⟨L, _, _, j, x, hx⟩
    let _ := j.toAlgebra
    have : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
    exact ⟨L, inferInstance, j.toAlgebra, Module.Finite.of_restrictScalars_finite ℚ _ _, x, hx⟩
  · rintro ⟨L, _, _, _, x, hx⟩
    exact ⟨L, inferInstance, NumberField.of_module_finite c.F L, algebraMap c.F L, x, hx⟩

theorem tanLin_iff : TanLin Xo ↔ CombLinearAt Xo c := by
  constructor
  · intro h S _ _ x m v hv
    refine ⟨fun cf => ?_, fun cf w hw => isTanAt_of_isCombAt hv hw,
      fun τ he cf w hw => isEigAt_of_isCombAt hv he hw, Formalism.L2.PjFree.isCombAt_single hv,
      fun n M w hw b z hz => ?_⟩
    · obtain ⟨w, hw⟩ := Formalism.L2.PjFree.isCombAt_exists hv cf
      exact ⟨w, hw, fun w' hw' => Formalism.L2.PjFree.isCombAt_unique hw' hw⟩
    · have := h S x v hv w (Matrix.of fun j i => M i j) b z hw hz
      convert this using 1
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
  · intro h S _ x m v hv m' w A N w' hw hw'
    let _ : Algebra ℚ S := ((Spec.preimage (x ≫ Xo.s)).hom.comp (algebraMap ℚ (KA l))).toAlgebra
    let _ : Algebra c.F (S ⊗[ℚ] c.F) := Algebra.TensorProduct.rightAlgebra
    let φ : S →+* S ⊗[ℚ] c.F := algebraMap _ _
    have : Epi (spMap (dualMap φ)) := epi_dualMap (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)
    obtain ⟨w₀, hw₀⟩ := Formalism.L2.PjFree.isCombAt_exists hv (A.mulVec N)
    have h1 := (h (S ⊗[ℚ] c.F) (spMap φ ≫ x) m _ (fun j => ReciprocityTheory.ChartRestriction.G.PullbackSections.tan_bc φ (hv j))).2.2.2.2 m'
      (fun i j => φ (A j i)) _ (fun i => isCombAt_bc φ (hw i)) _ _ (isCombAt_bc φ hw')
    have h2 := isCombAt_bc φ hw₀
    have e : (fun j => φ (A.mulVec N j)) = fun j => ∑ i, φ (N i) * φ (A j i) := by
      funext j
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [e] at h2
    rw [(cancel_epi _).1 (Formalism.L2.PjFree.isCombAt_unique h1 h2)]
    exact hw₀

def LieRebase : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (M : ∀ τ : E →+* ℂ, GL (Fin (Dw.mult τ)) T.V),
    letI := io.toAlgebra
    ∃ y' : IntFr Xo c T io, y'.1.x = y.1.x ∧ ∀ τ : E →+* ℂ,
      LieChange τ ((M τ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V).map (algebraMap T.V T.Fr)) y.1 y'.1

theorem intRebase_iff : IntRebase Xo c ↔ LieRebase Xo c := by
  constructor
  · intro h T io y M
    let _ := io.toAlgebra
    obtain ⟨y', -, hx, hu, -⟩ := h T io y y.1 rfl (fun τ => (M τ).1.transpose) fun τ => by
      rw [Matrix.det_transpose]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (M τ).isUnit
    exact ⟨y', hx, fun τ i => hu τ i⟩
  · intro h T io
    let _ := io.toAlgebra
    intro y z hz k hk
    have hk' : ∀ τ, IsUnit (k τ).transpose := fun τ =>
      (Matrix.isUnit_iff_isUnit_det _).2 (by rw [Matrix.det_transpose]; exact hk τ)
    obtain ⟨y', hx, hu⟩ := h T io y fun τ => (hk' τ).unit
    obtain ⟨a, ha, -⟩ := genScal_existsUnique z y'.1 (hx.trans hz.symm)
    exact ⟨y', (isUnit_of_genScal ha).unit, hx.trans hz.symm, fun τ i => hu τ i, (sClause_iff _ _ _).2 ha⟩

def IntFrLieGL : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io),
    letI := io.toAlgebra
    y'.1.x = y.1.x → ∀ τ : E →+* ℂ, ∃ M : GL (Fin (Dw.mult τ)) T.V,
      LieChange τ ((M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V).map (algebraMap T.V T.Fr)) y.1 y'.1

theorem intLieGL_iff (hS : SpreadSt Xo c) : IntLieGL Xo c ↔ IntFrLieGL Xo c :=
  ⟨fun h T io y y' => h T io y.1 y'.1 y.2.2 y'.2.2,
    fun h T io y y' hy hy' => letI := io.toAlgebra; h T io ⟨y, hS _ y, hy⟩ ⟨y', hS _ y', hy'⟩⟩

variable {Xo c}

theorem valV_unit {T : CDVR} {a : T.V} (ha : IsUnit a) : valV T.V (algebraMap T.V T.Fr a) = 1 :=
  ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_eq_one_iff_notMem).2 (IsLocalRing.notMem_maximalIdeal.2 ha)

theorem intDiagUnit_of_intFrameGL (h : IntFrameGL Xo c) : IntDiagUnit Xo c := by
  intro T io y y' t
  let _ := io.toAlgebra
  rintro ⟨hx, hu, hs⟩ o
  rcases o with _ | ⟨τ, i⟩
  · obtain ⟨a, ha⟩ := h.2 T io y.1 y'.1 y.2.2 y'.2.2 hx
    rw [(genScal_existsUnique y.1 y'.1 hx).unique ((sClause_iff _ _ _).1 hs) ha]
    exact valV_unit a.isUnit
  · obtain ⟨M, hM⟩ := h.1 T io y.1 y'.1 y.2.2 y'.2.2 hx τ
    choose cf h1 h2 h3 using hu τ
    have e : ∀ i j, cf i j = algebraMap T.V T.Fr (M.1 i j) := fun i =>
      congrFun ((y.1.basis τ _ (hx ▸ y'.1.tan τ i) (y'.1.eig τ i)).unique (h3 i) (hM i))
    have hT : M.1.BlockTriangular OrderDual.toDual := fun i j hij =>
      IsFractionRing.injective T.V T.Fr (by rw [← e, h2 i j hij, map_zero])
    have hd : IsUnit (∏ i, M.1 i i) := by
      rw [← Matrix.det_of_lowerTriangular _ hT]
      exact (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
    rw [← h1, e]
    exact valV_unit (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => M.1 i i) (Finset.mem_univ i)) hd)

theorem first_integral (hT : TanLin Xo) (hR : IntRebase Xo c) (hU : IntDiagUnit Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y z : IntFr Xo c T io) : letI := io.toAlgebra
    z.1.x = y.1.x → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), (∀ j, i ≤ j) → ∀ a : Fin (Dw.mult τ) → T.Fr,
      IsCombAt y.1.x (y.1.u τ) a (z.1.u τ i) → ∀ j, a j ∈ Set.range (algebraMap T.V T.Fr) := by
  let _ := io.toAlgebra
  intro hx
  have tz : ∀ τ i, IsTanAt y.1.x (z.1.u τ i) := fun τ i => hx ▸ z.1.tan τ i
  have ty : ∀ τ i, IsTanAt z.1.x (y.1.u τ i) := fun τ i => hx ▸ y.1.tan τ i
  choose a ha using fun τ i => (y.1.basis τ (z.1.u τ i) (tz τ i) (z.1.eig τ i)).exists
  choose b hb using fun τ i => (z.1.basis τ (y.1.u τ i) (ty τ i) (y.1.eig τ i)).exists
  let A : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => a τ i j
  have hAB : ∀ τ, A τ * (Matrix.of fun j i => b τ i j) = 1 := fun τ => by
    ext j i
    have hc := hT T.Fr y.1.x (y.1.u τ) (y.1.tan τ) (z.1.u τ) (A τ) (b τ i) (y.1.u τ i) (ha τ) (hx ▸ hb τ i)
    have := congrFun ((y.1.basis τ _ (y.1.tan τ i) (y.1.eig τ i)).unique hc
      (Formalism.L2.PjFree.isCombAt_single (y.1.tan τ) i)) j
    rw [Matrix.one_apply, ← Pi.single_apply, ← this]
    rfl
  have hdet : ∀ τ, (A τ).det ≠ 0 := fun τ => (Matrix.isUnit_det_of_right_inverse (hAB τ)).ne_zero
  choose k N hk hN hNd hAN using fun τ => iwasawa' (V := T.V) (A τ) (hdet τ)
  obtain ⟨y'', t0, hx'', hu'', hs''⟩ := hR T io y z.1 hx k hk
  have hb : FrBor (fun o => Option.casesOn o t0 (fun p => Units.mk0 (N p.1 p.2 p.2) (hNd p.1 p.2))) z.1 y''.1 := by
    refine ⟨hx'', fun τ i => ⟨fun j => N τ j i, rfl, fun j hij => hN τ hij, ?_⟩, hs''⟩
    obtain ⟨w', hw'⟩ := Formalism.L2.PjFree.isCombAt_exists (z.1.tan τ) (fun j => N τ j i)
    have hc := hT T.Fr y.1.x (y.1.u τ) (y.1.tan τ) (z.1.u τ) (A τ) (fun j => N τ j i) w' (ha τ) (hx ▸ hw')
    have hkc : (A τ).mulVec (fun j => N τ j i) = fun j => algebraMap T.V T.Fr (k τ j i) :=
      funext fun j => congrFun (congrFun (hAN τ) j) i
    rw [hkc] at hc
    rw [← Formalism.L2.PjFree.isCombAt_unique hc (hu'' τ i)]
    exact hw'
  intro τ i hi a' ha' j
  have hv : valV T.V (N τ i i) = 1 := hU T io z y'' _ hb (some ⟨τ, i⟩)
  have e : a τ i j * N τ i i = algebraMap T.V T.Fr (k τ j i) := by
    refine Eq.trans ?_ (congrFun (congrFun (hAN τ) j) i)
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun r _ hr => by
      rw [hN τ (lt_of_le_of_ne (hi r) hr.symm), mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
    rfl
  rw [(y.1.basis τ _ (tz τ i) (z.1.eig τ i)).unique ha' (ha τ i)]
  refine IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) ?_
  have h1 : valV T.V (a τ i j * N τ i i) ≤ 1 := by
    rw [e]; exact HeightOneSpectrum.valuation_le_one _ _
  rwa [map_mul, hv, _root_.mul_one] at h1

theorem coord_integral (hT : TanLin Xo) (hR : IntRebase Xo c) (hU : IntDiagUnit Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y z : IntFr Xo c T io) : letI := io.toAlgebra
    z.1.x = y.1.x → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ a : Fin (Dw.mult τ) → T.V,
      IsCombAt y.1.x (y.1.u τ) (fun j => algebraMap T.V T.Fr (a j)) (z.1.u τ i) := by
  classical
  let _ := io.toAlgebra
  intro hx τ i
  let i₀ : Fin (Dw.mult τ) := ⟨0, i.pos⟩
  let P : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)) := Function.update (fun _ => 1) τ (Equiv.swap i₀ i)
  obtain ⟨z', -, hx', hu', -⟩ := hR T io z z.1 rfl (fun τ => (P τ).permMatrix T.V) fun τ => by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (P τ).sign with h | h <;> simp [h]
  have e : z'.1.u τ i₀ = z.1.u τ i := by
    refine Formalism.L2.PjFree.isCombAt_unique (hu' τ i₀) ?_
    convert Formalism.L2.PjFree.isCombAt_single (z.1.tan τ) i using 1
    funext j
    simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]
  obtain ⟨a, ha⟩ := (y.1.basis τ (z.1.u τ i) (hx ▸ z.1.tan τ i) (z.1.eig τ i)).exists
  choose a₀ ha₀ using first_integral hT hR hU T io y z' (hx'.trans hx) τ i₀ (fun j => Nat.zero_le _) a (e ▸ ha)
  exact ⟨a₀, by rw [funext ha₀]; exact ha⟩

theorem intFrLieGL_of (hT : TanLin Xo) (hR : IntRebase Xo c) (hU : IntDiagUnit Xo c) : IntFrLieGL Xo c := by
  intro T io y z
  let _ := io.toAlgebra
  intro hx τ
  choose a ha using coord_integral hT hR hU T io y z hx τ
  choose b hb using coord_integral hT hR hU T io z y hx.symm τ
  have hBA : Matrix.of b * Matrix.of a = 1 := by
    ext i j
    have hc := hT T.Fr y.1.x (y.1.u τ) (y.1.tan τ) (z.1.u τ) (Matrix.of fun j i => algebraMap T.V T.Fr (a i j)) _
      (y.1.u τ i) ha (hx ▸ hb i)
    have := congrFun ((y.1.basis τ _ (y.1.tan τ i) (y.1.eig τ i)).unique hc
      (Formalism.L2.PjFree.isCombAt_single (y.1.tan τ) i)) j
    apply IsFractionRing.injective T.V T.Fr
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.single_apply] at this
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, map_sum, map_mul]
    rw [Finset.sum_congr rfl fun r _ => mul_comm _ _, this]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  exact ⟨⟨Matrix.of a, Matrix.of b, mul_eq_one_comm.1 hBA, hBA⟩, ha⟩

end GlobalTheory.ReframeClauses
