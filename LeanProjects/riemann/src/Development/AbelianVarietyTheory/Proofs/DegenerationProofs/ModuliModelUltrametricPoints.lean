import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetFactor

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.UnifModel

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {a : R →+* R₁} {b : R₁ →+* R₂}
    {d : R →+* R₂} (h : ∀ x, b (a x) = d x) : spMap b ≫ spMap a = spMap d := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show b.comp a = d from RingHom.ext h]

open IsLocalRing in

theorem exists_finite_split {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [IsAlgClosed Ω]
    (σ : ResidueField R →+* Ω) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
      (β : ResidueField R' →+* Ω), β.comp (ResidueField.map f) = σ → s ⊆ Set.range β →
      ∃ E : SplitExt (Sp (ResidueField R')),
        E.IsGt ((Over.pullback (spMap (residue R'))).obj ((Over.pullback (spMap f)).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  have := h₀.smooth
  have := h₀.quasiCompact
  have := h₀.separated
  obtain ⟨T⟩ := h₀.fibres _ (spMap σ)
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ _ T
  refine ⟨s, hs, fun R' _ _ f _ β hβ hr => ?_⟩
  obtain ⟨T'⟩ := H _ (ResidueField.map f) β hβ hr
  have e : spMap (ResidueField.map f) ≫ spMap (residue R) = spMap (residue R') ≫ spMap f :=
    (spMap_comp (d := (residue R').comp f) fun _ => rfl).trans (spMap_comp fun _ => rfl).symm
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback (spMap (residue R))).obj G) (spMap (ResidueField.map f))).comp
      (isGrpPullback_pullback G _)).congr e rfl)
    ((isGrpPullback_pullback ((Over.pullback (spMap f)).obj G) (spMap (residue R'))).comp (isGrpPullback_pullback G _))
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T'⟩

theorem iso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (Geo.Tor.chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem iso_comp {X Y Y' : Scheme.{0}} {B : LB Y'} {A : LB Y} {L : LB X} (hB : B.IsLB) (hA : A.IsLB) (hL : L.IsLB)
    {φ : Y ⟶ X} {h : Y' ⟶ Y} (H' : LBIso B (A.pull h)) (H : LBIso A (L.pull φ)) : LBIso B (L.pull (h ≫ φ)) :=
  H'.trans hB (pull_isLB hA _) (pull_isLB hL _) (iso_pull H h rfl)

theorem iso_of_map {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {G : Over S} {B : Over S'} {A : Over S''} [GrpObj G] [GrpObj B] [GrpObj A]
    {f : S' ⟶ S} {g : S'' ⟶ S'} {a : A.left ⟶ G.left} {b : B.left ⟶ G.left} (ha : IsGrpPullback A G (g ≫ f) a)
    (hb : IsGrpPullback B G f b) {L : LB G.left} {M : LB B.left} {N : LB A.left} (hL : L.IsLB) (hM : M.IsLB)
    (hN : N.IsLB) (eN : LBIso N (L.pull a)) (eM : LBIso M (L.pull b)) :
    ∃ φ : A.left ⟶ B.left, IsGrpPullback A B g φ ∧ LBIso N (M.pull φ) ∧
      ∀ (u : A ⟶ A) (v : B ⟶ B) (w : G.left ⟶ G.left), u.left ≫ a = a ≫ w → v.left ≫ b = b ≫ w →
        u.left ≫ φ = φ ≫ v.left := by
  let φ := hb.1.lift a (A.hom ≫ g) (by rw [ha.1.w, Category.assoc])
  have h₁ : φ ≫ b = a := hb.1.lift_fst _ _ _
  have h₂ : φ ≫ B.hom = A.hom ≫ g := hb.1.lift_snd _ _ _
  refine ⟨φ, hb.cancel (by rw [h₁]; exact ha) h₂,
    eN.trans hN (pull_isLB hL _) (pull_isLB hM _) (iso_pull eM φ h₁.symm).symm, fun u v w hu hv => ?_⟩
  apply hb.1.hom_ext
  · rw [Category.assoc, h₁, hu, Category.assoc, hv, ← Category.assoc, h₁]
  · rw [Category.assoc, h₂, Category.assoc, Over.w, h₂, ← Category.assoc, Over.w]

section Geometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem polAt_of_point {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) (χ : S ⟶ Y.X) (y : Sp K ⟶ Xo.XF c)
    (h : x ≫ χ = y ≫ Y.j) (t : SAB H S) (mp : SABMap t Y.t χ) : GlobalTheory.LN.PolAt t x := by
  have hN := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, ⟨w, hw⟩, -⟩ := exists_cancel (g := y) (f := Y.j)
    (((isGrpPullback_pullback t.G x).comp mp.cart).congr h rfl) Y.m.cart Y.t.PP.isLB Y.oF.t.PP.isLB hN
    (iso_pull (iso_of_map mp) _ rfl) (iso_of_map Y.m)
  have := Y.oF.proper
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  refine ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 this,
    relAmple_pull hφ.1 Y.oF.t.PP.isLB hN ((isGen_iff w).1 hw) U hU (fun z => ?_) Y.oF.ample,
    kTriv_pull hφ Y.oF.t.PP.isLB hN ((isGen_iff w).1 hw) Y.oF.ktriv⟩
  rwa [Subsingleton.elim z (IsLocalRing.closedPoint K)]

theorem exists_cart {V : Type} [CommRing V] [IsDomain V] {C : Type} [Field C] [Algebra (FractionRing V) C] {I : Ideal V}
    (χ : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (mp : SABMap t Y.t χ) (P : PELUnif I t) (y : Sp C ⟶ Xo.XF c)
    (h : jFK (R := V) C ≫ jK V ≫ χ = y ≫ Y.j) (o : Full D C) (ho : FullAt Y y o) :
    ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := V) C) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧
      letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left := by
  let := H.starRing
  obtain ⟨φ₀, h₀, e₀, a₀, -⟩ := ho
  have := P.U.gen_hom
  have hi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have : IsMonHom P.U.gen.symm.hom := inferInstanceAs (IsMonHom P.U.gen.inv)
  have hb : IsGrpPullback P.A.A Y.t.G (jK V ≫ χ) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) ≫ mp.cm.F) :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp ((isGrpPullback_pullback t.G (jK V)).comp mp.cart)).congr
      (Category.id_comp _) rfl
  have hN := pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK V))
  have e₁ : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK V))) := P.bundle ▸ P.U.ext
  have e₂ : LBIso P.A.L ((t.PP.L.pull (pullback.fst t.G.hom (jK V))).pull P.U.gen.inv.left) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (chartPullUnpull _ _ hi)
      (iso_pull e₁.symm P.U.gen.inv.left rfl) |>.symm
  obtain ⟨φ, hφ, eφ, aφ⟩ := exists_cancel (g := jFK (R := V) C) ((h₀.comp Y.m.cart).congr h.symm rfl) hb
    Y.t.PP.isLB P.A.isLB o.P.isLB (iso_comp o.P.isLB Y.oF.t.PP.isLB Y.t.PP.isLB e₀ (iso_of_map Y.m))
    (iso_comp P.A.isLB hN Y.t.PP.isLB e₂ (iso_pull (iso_of_map mp) _ rfl))
  refine ⟨φ, hφ, eφ, fun x => aφ _ _ (Y.t.act.act x).left ?_ ?_⟩
  · rw [← Category.assoc, a₀, Category.assoc, Y.m.act, Category.assoc]
  · have k₁ : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK V)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    have k₂ : ((Over.pullback (jK V)).map (t.act.act x)).left ≫ pullback.fst t.G.hom (jK V) =
        pullback.fst t.G.hom (jK V) ≫ (t.act.act x).left := pullback.lift_fst _ _ _
    rw [← Category.assoc, ← Over.comp_left, k₁, Over.comp_left, Category.assoc, Category.assoc, Category.assoc,
      ← mp.act]
    exact congrArg _ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) k₂).trans (Category.assoc _ _ _)))

end Geometry

theorem exists_finset_point {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : X ⟶ Sp ℚ) [LocallyOfFiniteType p]
    (a : Sp Ω ⟶ X) : ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (s : Set Ω) ⊆ Set.range β →
      ∃ b : Sp k ⟶ X, spMap β ≫ b = a := by
  first
  | (rename_i h_1 h_4; revert Ω h_1 X p h_4 a; exact @_root_.GlobalTheory.PointDescentFactorization.point_descends)
  | exact @_root_.GlobalTheory.PointDescentFactorization.point_descends
  | exact _root_.GlobalTheory.PointDescentFactorization.point_descends
  | (apply _root_.GlobalTheory.PointDescentFactorization.point_descends <;> assumption)
  | (intros; apply _root_.GlobalTheory.PointDescentFactorization.point_descends <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PointDescentFactorization.point_descends <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PointDescentFactorization.point_descends ..)

theorem isLocalHom_of_integral {V W Ω : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [CommRing Ω] [IsLocalRing Ω] (g : W →+* Ω)
    (h : ∀ v ∈ IsLocalRing.maximalIdeal V, g (algebraMap V W v) ∈ IsLocalRing.maximalIdeal Ω) : IsLocalHom g := by
  let P := (IsLocalRing.maximalIdeal Ω).comap g
  have hP : P.IsPrime := Ideal.comap_isPrime _ _
  have e : P.comap (algebraMap V W) = IsLocalRing.maximalIdeal V :=
    ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (Ideal.comap_isPrime _ P).ne_top h).symm
  have hm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := V) P
    (e ▸ IsLocalRing.maximalIdeal.isMaximal V)
  exact ((IsLocalRing.local_hom_TFAE g).out 4 0).1 (IsLocalRing.eq_maximalIdeal hm)

theorem cExt_of_integral {V W : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W]
    [Algebra V W] [Algebra.IsIntegral V W] {C : Type} [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing V) C] [Algebra (FractionRing W) C] (hV : CExt V (IsLocalRing.maximalIdeal V) C)
    (h : ∀ x, algebraMap (FractionRing W) C (algebraMap W _ (algebraMap V W x)) =
      algebraMap (FractionRing V) C (algebraMap V _ x)) : CExt W (IsLocalRing.maximalIdeal W) C := by
  let v := NormedField.valuation (K := C)
  have hv : ∀ x : C, x ∈ v.valuationSubring ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff]; exact NNReal.coe_le_coe.symm
  let g : W →+* C := (algebraMap (FractionRing W) C).comp (algebraMap W _)
  let g₀ : V →+* v.valuationSubring := (g.comp (algebraMap V W)).codRestrict _ fun x => (hv _).2 (by
    rw [RingHom.comp_apply, RingHom.comp_apply, h]; exact hV.1 x)
  have hg : ∀ x, g x ∈ v.valuationSubring := fun x => by
    have : IsIntegral v.valuationSubring (g x) :=
      IsIntegral.map_of_comp_eq g₀ g rfl (Algebra.IsIntegral.isIntegral (R := V) x)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact hy ▸ y.2
  have hm : ∀ x : v.valuationSubring, x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ ‖(x : C)‖ < 1 := fun x => by
    rw [Valuation.mem_maximalIdeal_iff]; exact NNReal.coe_lt_coe.symm
  have hl := isLocalHom_of_integral (V := V) (g.codRestrict _ hg) fun x hx => (hm _).2 (by
    show ‖algebraMap (FractionRing W) C (algebraMap W _ (algebraMap V W x))‖ < 1
    rw [h]; exact hV.2 x hx)
  exact ⟨fun r => (hv _).1 (hg r), fun r hr => (hm _).1 (map_nonunit (g.codRestrict _ hg) r hr)⟩

theorem isAlgClosed_of_surjective {V F Ω : Type} [CommRing V] [Field F] [IsAlgClosed F] [Algebra V F] [Field Ω]
    (ρ : integralClosure V F →+* Ω) (hρ : Function.Surjective ρ) : IsAlgClosed Ω := by
  refine IsAlgClosed.of_exists_root _ fun p hp hi => ?_
  obtain ⟨q, hq, hd, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective ρ hρ p)) hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero F q
    (by rw [hd]; exact (Polynomial.degree_pos_of_irreducible hi).ne')
  have hz' : IsIntegral V z := isIntegral_trans (A := integralClosure V F) z ⟨q, hm, hz⟩
  refine ⟨ρ ⟨z, hz'⟩, ?_⟩
  have : q.eval ⟨z, hz'⟩ = 0 := Subtype.val_injective
    ((Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := F) (⟨z, hz'⟩ : integralClosure V F) q).symm.trans hz)
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom, this, map_zero]

theorem exists_split (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F] [IsAlgClosed F]
    [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (G : Over (Sp V)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (W : Subalgebra V F) (_ : IsDiscreteValuationRing W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
      Module.Finite V W ∧
      GlobalTheory.LN.SplitOver ((Over.pullback (spMap (algebraMap V W))).obj G) (IsLocalRing.maximalIdeal W) := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (integralClosure V F)
  let := Ideal.Quotient.field m
  let ρ := Ideal.Quotient.mk m
  have := isAlgClosed_of_surjective ρ Ideal.Quotient.mk_surjective
  have hV : ∀ v ∈ IsLocalRing.maximalIdeal V, ρ (algebraMap V _ v) = 0 := fun v hv => by
    have := IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) m)
    rw [← this] at hv
    exact Ideal.Quotient.eq_zero_iff_mem.2 hv
  have l₀ : IsLocalHom (ρ.comp (algebraMap V _)) := isLocalHom_of_integral (V := V) _ fun v hv => by
    show ρ (algebraMap V _ v) ∈ _
    rw [hV v hv]; exact zero_mem _
  obtain ⟨s, hs, h⟩ := exists_finite_split
    (IsLocalRing.ResidueField.lift (ρ.comp (algebraMap V _))) G hG
  choose r hr using Ideal.Quotient.mk_surjective (I := m)
  obtain ⟨W, hd, hc, -, hf, -, hl, -, hW⟩ := exists_complete_dvr_finite_subalgebra V F
    (hs.toFinset.image fun x => (r x : F))
  have le : W ≤ integralClosure V F := fun x hx =>
    (Algebra.IsIntegral.isIntegral (R := V) (⟨x, hx⟩ : W)).map W.val
  let g := ρ.comp (Subalgebra.inclusion le).toRingHom
  have l₁ : IsLocalHom g := isLocalHom_of_integral (V := V) _ fun v hv => by
    show ρ (algebraMap V _ v) ∈ _
    rw [hV v hv]; exact zero_mem _
  refine ⟨W, hd, hc, hf, h W (algebraMap V W) (IsLocalRing.ResidueField.lift g) (RingHom.ext fun x => ?_) fun x hx => ?_⟩
  · obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  · exact ⟨IsLocalRing.residue W ⟨r x, hW _ (Finset.mem_image.2 ⟨x, hs.mem_toFinset.2 hx, rfl⟩) (r x).2⟩, hr x⟩

theorem epi_spMap {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective (Spec.map (CommRingCat.ofHom σ))

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem exists_finiteType (Xo : Moduli D l) (c : Coeff l) : ∃ p : Xo.XF c ⟶ Sp ℚ, LocallyOfFiniteType p := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := c.fin
  have : LocallyOfFiniteType (spMap (algebraMap ℚ c.F)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 inferInstance)
  exact ⟨pullback.snd _ _ ≫ spMap (algebraMap ℚ c.F), inferInstance⟩

theorem exists_split_point (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] (F : Type) [Field F] [IsAlgClosed F] [Algebra W F]
    [FaithfulSMul W F] [Algebra.IsAlgebraic W F] (y : Sp F ⟶ Xo.XF c) (b : O →+* W)
    (hy : y ≫ Y.j ≫ Y.s = spMap (algebraMap W F) ≫ spMap b) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (f : W →+* V) (i : V →+* F)
      (χ : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (_ : SABMap t Y.t χ), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
      f.Finite ∧ Function.Injective i ∧ (∀ x, i (f x) = algebraMap W F x) ∧ spMap i ≫ χ = y ≫ Y.j ∧
      GlobalTheory.LN.PolAt t (jK V) ∧ GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal V) := by
  obtain ⟨p, hp⟩ := exists_finiteType Xo c
  obtain ⟨s, hs⟩ := exists_finset_point p y
  obtain ⟨W₁, d₁, c₁, -, f₁, -, -, hW₁, -⟩ := exists_complete_dvr_finite_subalgebra W F s
  have i₁ : Function.Injective (algebraMap W₁ F) := Subtype.val_injective
  let β₁ : FractionRing W₁ →+* F := IsFractionRing.lift i₁
  have hβ₁ : ∀ x, β₁ (algebraMap W₁ _ x) = algebraMap W₁ F x := IsFractionRing.lift_algebraMap i₁
  obtain ⟨y₁, hy₁⟩ := hs _ β₁ fun x hx => by
    obtain ⟨u, hu, v, hv, h0, e⟩ := hW₁ x hx
    refine ⟨algebraMap W₁ _ ⟨u, hu⟩ / algebraMap W₁ _ ⟨v, hv⟩, ?_⟩
    rw [map_div₀, hβ₁, hβ₁]
    exact (div_eq_iff h0).2 e.symm
  have := epi_spMap β₁
  obtain ⟨χ₁, t₁, m₁, -, h₁, -⟩ := model_point_extends E H D l Xo c O β Y W₁ (FractionRing W₁)
    ((algebraMap W W₁).comp b) y₁ (by
      rw [← cancel_epi (spMap β₁), reassoc_of% hy₁, hy, ← Category.assoc, spMap_comp hβ₁,
        spMap_comp (d := (algebraMap W F).comp b) fun _ => rfl]
      exact (spMap_comp fun _ => rfl).symm)
  have : CharZero F := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective W F)
  have : Algebra.IsAlgebraic W₁ F := Algebra.IsAlgebraic.extendScalars (R := W)
    (FaithfulSMul.algebraMap_injective W W₁)
  obtain ⟨W₂, d₂, c₂, f₂, hsp⟩ := exists_split W₁ F t₁.G t₁.semi
  obtain ⟨PP', cub, sym, adj, prim, m₂, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap W₁ W₂)) t₁
  obtain ⟨m, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
  have j₂ : Function.Injective ((algebraMap W₂ (FractionRing W₂)).comp (algebraMap W₁ W₂)) :=
    (IsFractionRing.injective W₂ _).comp fun _ _ h => i₁ (congrArg (fun z : W₂ => (z : F)) h)
  let gm₂ : FractionRing W₁ →+* FractionRing W₂ := IsFractionRing.lift j₂
  refine ⟨W₂, inferInstance, inferInstance, d₂, (algebraMap W₁ W₂).comp (algebraMap W W₁), algebraMap W₂ F,
    spMap (algebraMap W₁ W₂) ≫ χ₁, _, m, c₂,
    (RingHom.finite_algebraMap.2 f₂).comp (RingHom.finite_algebraMap.2 f₁), Subtype.val_injective, fun _ => rfl, ?_,
    polAt_of_point Y _ _ (spMap gm₂ ≫ y₁) ?_ _ m, hsp⟩
  · rw [← hy₁, Category.assoc, ← h₁, ← Category.assoc, ← Category.assoc, spMap_comp hβ₁]
    exact congrArg (· ≫ χ₁) (spMap_comp fun _ => rfl)
  · rw [Category.assoc, ← h₁, ← Category.assoc, ← Category.assoc, spMap_comp (IsFractionRing.lift_algebraMap j₂)]
    exact congrArg (· ≫ χ₁) (spMap_comp fun _ => rfl)

end Main

theorem exists_mdl_torsionIso : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K] (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) → ∀ (y : Sp K ⟶ Xo.XF c) (b : c.V W₀ →+* W), y ≫ Y.j ≫ Y.s = spMap (algebraMap (FractionRing W) K) ≫ jK W ≫ spMap b → ∀ o : Full D C, FullAt Y (spMap gam ≫ y) o → ∃ (M : Mdl o) (f : W →+* M.W) (χ : Sp M.W ⟶ Y.X) (mp : SABMap M.t Y.t χ), f.Finite ∧ (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x)) ∧ jFK (R := M.W) C ≫ jK M.W ≫ χ = spMap gam ≫ y ≫ Y.j ∧ M.P.U.LG = M.t.PP ∧ M.P.TorsionIso := by
  intro _ _ hU _ _ _ _ E _ _ _ H D l Xo c W₀ Y C _ _ _ _ _ W _ _ _ _ ⟨d, hc, h0⟩ hext K _ _ _ gam hgam y b hy o ho
  let F := algebraicClosure (FractionRing W) C
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure (FractionRing W) C).isAlgClosed
  let g : K →ₐ[FractionRing W] C := ⟨gam, hgam⟩
  let g' : K →+* F := gam.codRestrict F fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic x).algHom g)
  let : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W _)).toAlgebra
  have : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).2
    ((algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _))
  have : Algebra.IsAlgebraic W F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := F)).2 inferInstance
  obtain ⟨V, _, _, dV, f, i, χ, t, mp, cV, hf, hi, hif, hχ, hpol, hsp⟩ := exists_split_point Y W F (spMap g' ≫ y) b (by
    rw [Category.assoc, hy, ← Category.assoc, spMap_comp (d := algebraMap (FractionRing W) F)
      fun x => Subtype.ext (hgam x), ← Category.assoc]
    exact congrArg (· ≫ spMap b) (spMap_comp fun _ => rfl))
  have hi' : Function.Injective ((algebraMap F C).comp i) := (algebraMap F C).injective.comp hi
  let : Algebra (FractionRing V) C := (IsFractionRing.lift hi' : FractionRing V →+* C).toAlgebra
  have hV : ∀ x, algebraMap (FractionRing V) C (algebraMap V _ x) = algebraMap F C (i x) :=
    IsFractionRing.lift_algebraMap hi'
  have hVW : ∀ x, algebraMap (FractionRing V) C (algebraMap V _ (f x)) =
      algebraMap (FractionRing W) C (algebraMap W _ x) := fun x => by rw [hV, hif]; rfl
  have : CharZero V := ((algebraMap F C).comp i).charZero
  let : Algebra W V := f.toAlgebra
  have : Module.Finite W V := hf
  obtain ⟨P, hP⟩ := hU E H V ⟨dV, cV, inferInstance⟩ t hpol hsp
  have hgen : jFK (R := V) C ≫ jK V ≫ χ = (spMap gam ≫ y) ≫ Y.j := by
    have e₁ : spMap (algebraMap F C) ≫ spMap g' = spMap gam := spMap_comp fun _ => rfl
    have e₂ : spMap (algebraMap F C) ≫ spMap i = jFK (R := V) C ≫ jK V :=
      (spMap_comp (d := (algebraMap F C).comp i) fun _ => rfl).trans (spMap_comp hV).symm
    rw [← reassoc_of% e₂, hχ, ← e₁]
    simp only [Category.assoc]
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_cart Y χ t mp P _ hgen o ho
  exact ⟨⟨V, ⟨dV, cV, inferInstance⟩, cExt_of_integral hext hVW, t, P, φ, h₁, h₂, h₃⟩, f,
    χ, mp, hf, hVW, hgen.trans (Category.assoc _ _ _), P.bundle, hP⟩

theorem exists_mdl : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K] (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) → ∀ (y : Sp K ⟶ Xo.XF c) (b : c.V W₀ →+* W), y ≫ Y.j ≫ Y.s = spMap (algebraMap (FractionRing W) K) ≫ jK W ≫ spMap b → ∀ o : Full D C, FullAt Y (spMap gam ≫ y) o → ∃ (M : Mdl o) (f : W →+* M.W) (χ : Sp M.W ⟶ Y.X) (mp : SABMap M.t Y.t χ), f.Finite ∧ (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x)) ∧ jFK (R := M.W) C ≫ jK M.W ≫ χ = spMap gam ≫ y ≫ Y.j ∧ M.P.U.LG = M.t.PP := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y C _ _ _ _ _ W _ _ _ _ hW hext K _ _ _ gam hgam y b hy o ho
  obtain ⟨M, f, χ, mp, k₁, k₂, k₃, k₄, -⟩ :=
    exists_mdl_torsionIso h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y C W hW hext K gam hgam y b hy o ho
  exact ⟨M, f, χ, mp, k₁, k₂, k₃, k₄⟩

end GlobalTheory.Ex.UnifModel
