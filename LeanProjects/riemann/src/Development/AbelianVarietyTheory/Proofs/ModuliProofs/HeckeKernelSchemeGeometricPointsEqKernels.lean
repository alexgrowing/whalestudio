import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNsmulOfDvd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtSetOfLists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPts

theorem exists_geomPt (S : Scheme.{0}) (p : S) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S), Set.range x = {p} := by
  refine ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) (AlgebraicClosure (S.residueField p))))
      ≫ S.fromSpecResidueField p, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨IsLocalRing.closedPoint _, ?_⟩, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

theorem eq_comp_section {S X : Scheme.{0}} (g : X ⟶ S) [IsSeparated g] (τ : S ⟶ X) (w : τ ≫ g = 𝟙 S) {k : Type}
    [Field k] (x : Sp k ⟶ S) (z : Sp k ⟶ X) (hz : z ≫ g = x)
    (h : z (IsLocalRing.closedPoint k) ∈ Set.range τ) : x ≫ τ = z := by
  have : IsClosedImmersion (τ ≫ g) := by rw [w]; infer_instance
  have : IsClosedImmersion τ := IsClosedImmersion.of_comp _ g
  have : Surjective (pullback.fst z τ) := ⟨fun q => by
    rw [← Set.mem_range, Scheme.Pullback.range_fst, Subsingleton.elim q (IsLocalRing.closedPoint k)]
    exact h⟩
  have : IsIso (pullback.fst z τ) := isIso_of_isClosedImmersion_of_surjective _
  have e : (inv (pullback.fst z τ) ≫ pullback.snd z τ) ≫ τ = z := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  rw [← hz, ← e]
  simp only [Category.assoc, reassoc_of% w]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {J : Type}
    (σ : J → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (σ j).left) ↔ ∃ j, toUnit (Over.mk x) ≫ σ j = z := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨IsLocalRing.closedPoint k, rfl⟩)
    exact ⟨j, Over.OverMorphism.ext (eq_comp_section G.hom (σ j).left (Over.w _) x z.left (Over.w z) hj)⟩
  · rintro ⟨j, rfl⟩ _ ⟨q, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, _, (Scheme.Hom.comp_apply _ _ _).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {P : Ideal (𝓞 E)} {p i : ℕ}

theorem heckeSet_eq {S : Scheme.{0}} {t : SAB H S} {K K' : Set t.G.left} (hp : p ≠ 0) (h : HeckeSet D t P p i K)
    (h' : HeckeSet D t P p i K') (hle : K ⊆ K') : K = K' := by
  refine hle.antisymm fun g hg => ?_
  obtain ⟨k, _, _, z, hz⟩ := exists_geomPt _ g
  obtain ⟨C, hC, hk⟩ := h k (z ≫ t.G.hom)
  obtain ⟨C', hC', hk'⟩ := h' k (z ≫ t.G.hom)
  have : Finite C' := Nat.finite_of_card_ne_zero (by rw [hk'.2.2.2.2.1]; exact pow_ne_zero _ hp)
  have e : C = C' := Subgroup.eq_of_le_of_card_ge (fun u hu => (hC' u).2 (((hC u).1 hu).trans hle))
    (by rw [hk.2.2.2.2.1, hk'.2.2.2.2.1])
  have m : (Over.homMk z rfl : Over.mk (z ≫ t.G.hom) ⟶ t.G) ∈ C := by
    rw [e, hC']
    exact hz.subset.trans (Set.singleton_subset_iff.2 hg)
  exact (hC _).1 m (hz.symm.subset rfl)

theorem pow_eq_one {S : Scheme.{0}} {t : SAB H S} {T : Over S} {C : Subgroup (T ⟶ t.G)} (hp : (p : 𝓞 E) ∈ P)
    (h : t.HeckeKer T D P p i C) {x : T ⟶ t.G} (hx : x ∈ C) : x ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span t x (p ^ 2)).1 fun a ha => h.2.2.1 hx a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp
  rwa [map_natCast] at this

theorem exists_set (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp (KA l)} (o : Ob D l s)
    (C : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G)) (h : o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C) :
    ∃ K : Set o.t.G.left, EtSet o.t.G K ∧ HeckeSet D o.t P p i K ∧ (∀ z, z ∈ C ↔ Set.range z.left ⊆ K) ∧
      ∀ K', (∀ z ∈ C, Set.range z.left ⊆ K') → K ⊆ K' := by
  have := o.proper
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [h.2.2.2.2.1]; exact pow_ne_zero _ hA.2.2.1.ne_zero)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let σ : Fin n → (𝟙_ (Over (Sp k)) ⟶ o.t.G) := fun j => (e.symm j).1
  have tu : ∀ j, toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j = (e.symm j).1 := fun j => by
    apply Over.OverMorphism.ext
    simp [σ]
  have hσ : ∀ j, σ j ^ p ^ 2 = 1 := fun j => pow_eq_one (T := 𝟙_ (Over (Sp k))) hA.2.2.2.1 h (e.symm j).2
  have hC : (C : Set _) = Set.range (fun j => toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j) := by
    ext z
    refine ⟨fun hz => ⟨e ⟨z, hz⟩, by simp only [tu, Equiv.symm_apply_apply]⟩, ?_⟩
    rintro ⟨j, rfl⟩
    simp only [tu]
    exact (e.symm j).2
  obtain ⟨V, -, hV⟩ := GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel E H D l P p i n _ s o σ hA hσ
  have h1 : Set.range (𝟙 (Sp k) :) ⊆ V := (hV k _).2 ⟨fun a b hab => e.symm.injective (Subtype.ext
    (Over.OverMorphism.ext (by simpa [σ] using hab))), C, hC, h⟩
  have h2 := fun (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) =>
    (hV k' x).1 fun q _ => h1 ⟨q, rfl⟩
  refine ⟨⋃ j, Set.range (σ j).left, ?_, fun k' _ _ x => ?_, fun z => ?_, fun K' hK' => ?_⟩
  · obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_id o.t
    refine GlobalTheory.HkFam.etSet_of_lists _ _ (𝟙 _) o.t.G o.t.G m.φ (p ^ 2) n σ _
      ⟨o.t.semi.comm, o.t.semi.smooth, inferInstance, o.t.semi.geomConnected⟩ m.cart ?_ inferInstance inferInstance
      inferInstance ⟨hσ, by rw [hm]; rfl, fun k' _ _ x => (h2 k' x).1⟩
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  · obtain ⟨C', hC', hk⟩ := (h2 k' x).2
    refine ⟨C', fun z => ?_, hk⟩
    rw [range_subset_iff, ← SetLike.mem_coe, hC']
    rfl
  · rw [range_subset_iff, ← SetLike.mem_coe, hC]
    rfl
  · exact Set.iUnion_subset fun j => hK' _ (e.symm j).2

theorem existsUnique_carries {Xo : Moduli D l} (Z : KerScheme Xo P p i) (hA : admitted l P p) (k : Type) [Field k]
    [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (h : Xo.univ.t.HeckeKer (Over.mk y) D P p i C) : ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y rfl rfl
    (by simp [spMap]) Xo.univ
  have key : ∀ y' : Sp k ⟶ Xo.X, 𝟙 _ ≫ y = y' → ∀ C : Subgroup (Over.mk y' ⟶ Xo.univ.t.G),
      Xo.univ.t.HeckeKer (Over.mk y') D P p i C → ∃ C' : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C' ∧
      ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk y' ⟶ Xo.univ.t.G), v.left = u.left ≫ m.toSABMap.φ →
        (u ∈ C' ↔ v ∈ C) := by
    rintro _ rfl C h
    obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk (𝟙 (Sp k)))
    have hh : ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk (𝟙 _ ≫ y) ⟶ Xo.univ.t.G),
        v.left = u.left ≫ m.toSABMap.φ → (u ∈ Subgroup.comap ρ.toMonoidHom C ↔ v ∈ C) := fun u v e => by
      rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
      rfl
    exact ⟨_, (GlobalTheory.HkSetPull.heckeKer_iff D P p i m.toSABMap (Over.mk (𝟙 (Sp k))) _ C hh).2 h, hh⟩
  obtain ⟨C', h', hCC⟩ := key y (Category.id_comp _) C h
  obtain ⟨K, het, hK, hmem, hmin⟩ := exists_set hA o C' h'
  obtain ⟨z, ⟨hz, n, hn⟩, huniq⟩ := Z.rep _ (y ≫ Xo.s) inferInstance o K het hK
  have cc := fun z : Sp k ⟶ Z.Hk => (GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₁ o).2
    Z.π₁ z Z.m₁
  have pre : ∀ {z : Sp k ⟶ Z.Hk} (n : ObjMap o Z.o₁ z) (w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      Set.range (w.left ≫ n.toSABMap.φ) ⊆ Z.K ↔ Set.range w.left ⊆ n.toSABMap.φ ⁻¹' Z.K := fun n w => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_subset_iff]
  refine ⟨z, ?_, fun z' hz' => huniq z' ?_⟩
  · obtain ⟨m', hm'⟩ := (cc z).1 n
    have e : z ≫ Z.π₁ = y := (Xo.rep _ (y ≫ Xo.s) inferInstance o).unique
      ⟨(Category.assoc _ _ _).trans hz, ⟨m'⟩⟩ ⟨rfl, ⟨m⟩⟩
    have rigid : ∀ (y' : Sp k ⟶ Xo.X) (m' : ObjMap o Xo.univ y'), y = y' → m'.toSABMap.φ = m.toSABMap.φ := by
      rintro _ m' rfl
      exact GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o y (.inl inferInstance) _ _
        fun a => ⟨_, m'.eta a, m.eta a⟩
    refine ⟨e, fun u v huv => ?_⟩
    let w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G := Over.homMk (n.cart.1.lift u.left (𝟙 _) (by simpa using Over.w u))
      (n.cart.1.lift_snd _ _ _)
    have hw : w.left ≫ n.toSABMap.φ = u.left := n.cart.1.lift_fst _ _ _
    rw [← hCC w v (by rw [huv, ← hw, Category.assoc, ← hm', rigid _ m' e.symm]), hmem, hn, ← pre, hw]
  · obtain ⟨rfl, hc⟩ := hz'
    obtain ⟨n', hn'⟩ := (cc z').2 m
    refine ⟨(Category.assoc _ _ _).symm, n', heckeSet_eq hA.2.2.1.ne_zero hK
      (GlobalTheory.HkSetPull.heckeSet_pull D P p i n'.toSABMap _ Z.hecke) (hmin _ fun w hw => ?_)⟩
    have ww : w.left ≫ o.t.G.hom = 𝟙 _ := Over.w w
    let u : Over.mk z' ⟶ Z.o₁.t.G := Over.homMk (w.left ≫ n'.toSABMap.φ) (by
      rw [Category.assoc, n'.cart.1.w, reassoc_of% ww]; rfl)
    let v : Over.mk (z' ≫ Z.π₁) ⟶ Xo.univ.t.G := Over.homMk (w.left ≫ m.toSABMap.φ) (by
      rw [Category.assoc, m.cart.1.w, reassoc_of% ww]; rfl)
    exact (pre n' w).1 ((hc u v ((congrArg (w.left ≫ ·) hn').trans (Category.assoc _ _ _).symm)).2 ((hCC w v rfl).1 hw))

end GlobalTheory.HkPts

theorem GlobalTheory.kerScheme_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo 𝔓 p i), admitted l 𝔓 p → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C → ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C) ∧ (i ≤ D.p + D.q → Surjective Z.π₁) := by
  intro E _ _ _ H D l Xo P p i Z hA
  refine ⟨GlobalTheory.HkPts.existsUnique_carries Z hA, fun hi => ⟨fun q => ?_⟩⟩
  obtain ⟨k, _, _, y, hy⟩ := GlobalTheory.HkPts.exists_geomPt _ q
  obtain ⟨C, hC⟩ := GlobalTheory.exists_heckeKer E H D l Xo P p i hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 hi k y
  obtain ⟨z, ⟨rfl, -⟩, -⟩ := GlobalTheory.HkPts.existsUnique_carries Z hA k y C hC
  obtain ⟨a, ha⟩ := hy.symm.subset rfl
  exact ⟨z a, (Scheme.Hom.comp_apply _ _ _).symm.trans ha⟩
