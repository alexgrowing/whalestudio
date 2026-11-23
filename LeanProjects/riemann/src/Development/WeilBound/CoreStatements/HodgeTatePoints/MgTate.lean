import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.WeilBound.CoreStatements.HodgeTatePoints.MgLevel

noncomputable section

namespace PositivityTheory.HtPt.Mg

section Pairing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem surjective_appTop_of_iso' {X Y : Scheme.{0}} (f : X ≅ Y) : Function.Surjective f.hom.appTop.hom := by
  have h : f.inv.appTop ≫ f.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  intro x
  refine ⟨f.inv.appTop.hom x, ?_⟩
  have hx := congrArg (fun g => g.hom x) h
  simpa using hx

theorem surj_fst_of_proper (hA : IsSemiAbelian A) (T : Over S) (hT : IsProper (pullback.snd A.hom T.hom)) :
    Function.Surjective (fst T A).left.appTop.hom := by
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI hAb : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    ⟨inferInstance, (inferInstance : Smooth (pullback.snd A.hom T.hom)), hT,
      (inferInstance : GeometricallyConnected (pullback.snd A.hom T.hom))⟩
  have hb := (GlobalTheory.ExpansionTotal.globalFns T.left ((Over.pullback T.hom).obj A) hAb).2
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom := by
    simp
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Surjective.comp (surjective_appTop_of_iso' _) hb

omit [GrpObj A] in
theorem proper_of_hom {T T' : Over S} (h : T' ⟶ T) (hT : IsProper (pullback.snd A.hom T.hom)) :
    IsProper (pullback.snd A.hom T'.hom) := by
  have e : h.left ≫ T.hom = T'.hom := Over.w h
  have q : pullback.snd A.hom (h.left ≫ T.hom) =
      (pullbackLeftPullbackSndIso A.hom T.hom h.left).inv ≫ pullback.snd (pullback.snd A.hom T.hom) h.left := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  have hp : IsProper (pullback.snd A.hom (h.left ≫ T.hom)) := by
    rw [q]
    infer_instance
  rwa [e] at hp

theorem tval_div' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (x : T ⟶ A) (z : Z) (J)
    (hJ : Good L z J) :
    tval θ r z J * (tval θ' r z J)⁻¹ =
      tval θ (r ≫ (translT A x).left) z J * (tval θ' (r ≫ (translT A x).left) z J)⁻¹ := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  exact val_div_eq hL (fst T A).left hT hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ

private theorem mul_eq_mul_mul_of_ratio_eq {G : Type*} [CommGroup G] {a a' b b' c c' d d' u : G}
    (h1 : a' * a⁻¹ = b' * b⁻¹) (h2 : c' * c⁻¹ = d' * d⁻¹) (h0 : a * d = c * b * u) :
    a' * d' = c' * b' * u := by
  have hb : b' = a' * a⁻¹ * b := by rw [h1]; group
  have hd : d' = c' * c⁻¹ * d := by rw [h2]; group
  have hd0 : d = a⁻¹ * (c * b * u) := by rw [← h0]; group
  rw [hb, hd, hd0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commIsOf_change' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have h1 := tval_div' hL hT θx' θx hx r θy.pt z J hJ
  have h2 := tval_div' hL hT θy' θy hy r θx.pt z J hJ
  have h0 := H Z r z J hJ
  rw [hx, hy]
  exact mul_eq_mul_mul_of_ratio_eq h1 h2 h0

theorem weilIs_pull_of_proper (hA : IsSemiAbelian A) (hL : L.IsLB) {T T' : Over S}
    (hT : IsProper (pullback.snd A.hom T'.hom)) (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hpV, ⟨θx0, θy0, hx0, hy0⟩, hall⟩ := H (h.left p)
  let V' : T'.left.Opens := h.left ⁻¹ᵁ V
  let g : overRes V' ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    simp only [overRes, Over.mk_hom]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w h])
  have key : g ≫ overResι V = overResι V' ≫ h := by
    ext
    simp [g, overResι, morphismRestrict_ι, V']
  have hsurj : Function.Surjective (fst (overRes V') A).left.appTop.hom :=
    surj_fst_of_proper hA _ (proper_of_hom (overResι V') hT)
  have hc : unitRes V' (Units.map h.left.appTop.hom.toMonoidHom c) =
      Units.map g.left.appTop.hom.toMonoidHom (unitRes V c) := by
    have hl := congrArg Over.Hom.left key
    simp only [Over.comp_left, overResι, Over.homMk_left] at hl
    ext
    simp only [unitRes, Units.coe_map, MonoidHom.coe_coe]
    have hv := congrArg (fun f => f.appTop.hom (c : Γ(T.left, ⊤))) hl
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hv
    exact hv.symm
  obtain ⟨θx', θy', hx', hy', hcc⟩ := exists_commIsOf_pull hL g (hall θx0 θy0 hx0 hy0)
  refine ⟨V', hpV, ⟨θx', θy', ?_, ?_⟩, ?_⟩
  · rw [hx', hx0, ← Category.assoc, key, Category.assoc]
  · rw [hy', hy0, ← Category.assoc, key, Category.assoc]
  · intro θx θy hx hy
    rw [hc]
    refine commIsOf_change' hL hsurj ?_ ?_ hcc
    · rw [hx, hx', hx0, ← Category.assoc, ← key, Category.assoc]
    · rw [hy, hy', hy0, ← Category.assoc, ← key, Category.assoc]

end Pairing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem exists_section_of_finite {Z : Scheme.{0}} {k K : Type} [Field k] [IsAlgClosed k] [Field K] (i : k →+* K)
    (f : Z ⟶ Sp k) [LocallyOfFiniteType f] (hf : Finite {p : Sp k ⟶ Z // p ≫ f = 𝟙 _}) (w : Sp K ⟶ Z)
    (hw : w ≫ f = spMap i) : ∃ p : Sp k ⟶ Z, p ≫ f = 𝟙 _ ∧ w = spMap i ≫ p := by
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace f
  haveI : Finite (closedPoints Z) := Finite.of_equiv _ (pointEquivClosedPoint f)
  have hz : IsClosed ({w (IsLocalRing.closedPoint K)} : Set Z) := by
    set z := w (IsLocalRing.closedPoint K)
    have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (isClosed_closure (s := ({z} : Set Z))).isLocallyClosed
    have hfin : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
      (Set.toFinite (closedPoints Z)).subset Set.inter_subset_right
    have hcl : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
      rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
      exact hfin.isClosed_biUnion (fun c hc => hc.2)
    rw [hcl.closure_eq] at h1
    have hm : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
      rw [h1]
      first
        | exact subset_closure (Set.mem_singleton z)
        | exact subset_closure (subset_closure (Set.mem_singleton z))
    exact hm.2
  refine ⟨pointOfClosedPoint f _ hz, pointOfClosedPoint_comp f _ hz, ?_⟩
  have hdesc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z w
  set φ := Z.descResidueField (Scheme.stalkClosedPointTo w)
  have hφ : Spec.map φ = spMap i ≫ Spec.map (residueFieldIsoBase f _ hz).hom := by
    have e1 : w ≫ f = Spec.map φ ≫ Spec.map (residueFieldIsoBase f _ hz).inv := by
      rw [SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdesc]
    rw [← hw, e1, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.comp_id]
  rw [pointOfClosedPoint, ← Category.assoc, ← hφ, hdesc]

theorem torsion_desc {X : Scheme.{0}} (G : Over X) [GrpObj G] [LocallyOfFiniteType G.hom] {k K : Type} [Field k]
    [IsAlgClosed k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) (n : ℕ) (hf : Finite {g : Over.mk x ⟶ G // g ^ n = 1})
    (g : Over.mk (spMap i ≫ x) ⟶ G) (hg : g ^ n = 1) : ∃ y : Over.mk x ⟶ G, y ^ n = 1 ∧ extPt i x ≫ y = g := by
  let Kn : Over X := pullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)
  let π : Kn ⟶ G := pullback.fst _ _
  have hπ0 : π ≫ (𝟙 G) ^ n = 1 := by
    rw [pullback.condition, comp_one]
  have hπ : ∀ {Y : Over X} (q : Y ⟶ Kn), (q ≫ π) ^ n = 1 := by
    intro Y q
    rw [← Category.comp_id (q ≫ π), ← comp_pow, Category.assoc, hπ0, comp_one]
  have hmk : ∀ {Y : Over X} (a : Y ⟶ G), a ^ n = 1 → a ≫ (𝟙 G) ^ n = toUnit Y ≫ (1 : 𝟙_ (Over X) ⟶ G) := by
    intro Y a ha
    rw [comp_pow, Category.comp_id, ha, comp_one]
  have hfac : ∀ {Y : Over X} (a : Y ⟶ G) (ha : a ^ n = 1) (q : Y ⟶ Kn), q ≫ π = a →
      q = pullback.lift a (toUnit Y) (hmk a ha) := by
    intro Y a ha q hq
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hq
    · exact Subsingleton.elim _ _
  haveI h1lft : LocallyOfFiniteType (1 : 𝟙_ (Over X) ⟶ G).left := by
    have hc : (1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom = 𝟙 _ := Over.w _
    haveI : LocallyOfFiniteType ((1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  haveI hπlft : LocallyOfFiniteType π.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      ((IsPullback.of_hasPullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)).map (Over.forget X)).flip h1lft
  haveI : LocallyOfFiniteType Kn.hom := by
    rw [← Over.w π]
    infer_instance
  let fZ : pullback Kn.hom x ⟶ Sp k := pullback.snd Kn.hom x
  have hq : ∀ p : Sp k ⟶ pullback Kn.hom x, p ≫ fZ = 𝟙 _ →
      (p ≫ pullback.fst Kn.hom x) ≫ Kn.hom = (Over.mk x).hom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ fZ) ≫ x = x
    rw [hp, Category.id_comp]
  have hfin : Finite {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _} := by
    refine Finite.of_surjective (fun a : {a : Over.mk x ⟶ G // a ^ n = 1} =>
      (⟨pullback.lift (pullback.lift a.1 (toUnit _) (hmk a.1 a.2)).left (𝟙 _)
        (by rw [Over.w, Category.id_comp]; rfl), pullback.lift_snd _ _ _⟩ :
        {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _})) ?_
    rintro ⟨p, hp⟩
    let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
    refine ⟨⟨q ≫ π, hπ q⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hfac (q ≫ π) (hπ q) q rfl]
      rfl
    · rw [pullback.lift_snd]
      exact hp.symm
  let w : Sp K ⟶ pullback Kn.hom x := pullback.lift (pullback.lift g (toUnit _) (hmk g hg)).left (spMap i)
    (by rw [Over.w]; rfl)
  obtain ⟨p, hp, hwp⟩ := exists_section_of_finite i fZ hfin w (pullback.lift_snd _ _ _)
  let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
  refine ⟨q ≫ π, hπ q, ?_⟩
  ext
  have e1 : w ≫ pullback.fst Kn.hom x = (pullback.lift g (toUnit _) (hmk g hg)).left := pullback.lift_fst _ _ _
  have e2 := congrArg Over.Hom.left (pullback.lift_fst g (toUnit _) (hmk g hg))
  rw [Over.comp_left] at e2
  rw [← e2, ← e1, hwp]
  simp [q, extPt, π]

theorem unitOn_map {k K : Type} [Field k] [Field K] (i : k →+* K) (c : kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  have := congrArg (fun q => q.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))
  exact this.symm

end PositivityTheory.HtPt.Mg
