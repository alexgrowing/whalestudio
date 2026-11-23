import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSetDesc

theorem exists_lift {S S' : Scheme.{0}} (f : S' ⟶ S) [Surjective f] {k : Type} [Field k] (x : Sp k ⟶ S) :
    ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (β : k →+* k') (x' : Sp k' ⟶ S'), x' ≫ f = spMap β ≫ x := by
  obtain ⟨s', hs'⟩ := Surjective.surj (f := f) (x.base (IsLocalRing.closedPoint k))
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := x) s' (IsLocalRing.closedPoint k) hs'
  obtain ⟨g, hg⟩ : ∃ g : Spec ((pullback f x).residueField q) ⟶ Sp k,
      g = (pullback f x).fromSpecResidueField q ≫ pullback.snd f x := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Spec ((pullback f x).residueField q) ⟶ S',
      h = (pullback f x).fromSpecResidueField q ≫ pullback.fst f x := ⟨_, rfl⟩
  have hgh : h ≫ f = g ≫ x := by
    rw [hg, hh, Category.assoc, Category.assoc, pullback.condition]
  let j := algebraMap ((pullback f x).residueField q) (AlgebraicClosure ((pullback f x).residueField q))
  refine ⟨AlgebraicClosure ((pullback f x).residueField q), inferInstance, inferInstance,
    j.comp (Spec.preimage g).hom, Spec.map (CommRingCat.ofHom j) ≫ h, ?_⟩
  have hβ : spMap (j.comp (Spec.preimage g).hom) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (Spec.preimage g) := by
    rw [← Spec.map_comp]
    rfl
  rw [hβ, Spec.map_preimage, Category.assoc, Category.assoc, hgh]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_torsion {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    Nat.card {x : Q // x ^ n = 1} = (nsmulAddMonoidHom (α := D.La) n).range.index := by
  have h1 : ∀ a : D.La, I.ev n a = 1 ↔ a ∈ (nsmulAddMonoidHom (α := D.La) n).range := by
    intro a
    rw [I.ker n hn a, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  let φ : D.La →+ Additive Q :=
    { toFun := fun a => Additive.ofMul (I.ev n a)
      map_zero' := by
        show Additive.ofMul (I.ev n 0) = Additive.ofMul 1
        rw [(h1 0).2 (zero_mem _)]
      map_add' := fun a b => by
        show Additive.ofMul (I.ev n (a + b)) = Additive.ofMul (I.ev n a * I.ev n b)
        rw [I.add] }
  have hker : φ.ker = (nsmulAddMonoidHom (α := D.La) n).range := by
    ext a
    rw [AddMonoidHom.mem_ker, ← h1]
    exact ofMul_eq_zero
  let σ : {x : Q // x ^ n = 1} ≃ φ.range :=
    { toFun := fun x => ⟨Additive.ofMul x.1, by
        obtain ⟨a, ha⟩ := (I.onto n hn x.1).1 x.2
        exact ⟨a, by show Additive.ofMul (I.ev n a) = Additive.ofMul x.1; rw [ha]⟩⟩
      invFun := fun y => ⟨Additive.toMul y.1, by
        obtain ⟨a, ha⟩ := y.2
        rw [← ha]
        exact (I.onto n hn _).2 ⟨a, rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr σ, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, hker,
    AddSubgroup.index_eq_card]

theorem index_ne_zero (D : Datum H) {n : ℕ} (hn : 0 < n) :
    (nsmulAddMonoidHom (α := D.La) n).range.index ≠ 0 := by
  have : Module.Finite (𝓞 E) D.La := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : Finite (D.La ⧸ (nsmulAddMonoidHom (α := D.La) n).range) := by
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨a, rfl⟩
  exact AddSubgroup.index_ne_zero_of_finite

theorem torsion_onto {D : Datum H} {k k' : Type} [Field k] [Field k'] {Q Q' : Type} [Group Q] [Group Q']
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} {act' : 𝓞 E → Q' → Q'} {e' : ℕ → Q' → Q' → k'ˣ → Prop}
    (I : TateIso D k Q act e) (I' : TateIso D k' Q' act' e') (r : Q →* Q') (hr : Function.Injective r)
    {n : ℕ} (hn : 0 < n) (y : Q') (hy : y ^ n = 1) : ∃ x, r x = y := by
  have hA := card_torsion I hn
  have hB := card_torsion I' hn
  have : Finite {x : Q' // x ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [hB]; exact index_ne_zero D hn)
  let g : {x : Q // x ^ n = 1} → {x : Q' // x ^ n = 1} := fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
  have hg : Function.Injective g := fun a b hab => Subtype.ext (hr (congrArg Subtype.val hab))
  obtain ⟨x, hx⟩ := (hg.bijective_of_nat_card_le (by rw [hA, hB])).2 ⟨y, hy⟩
  exact ⟨x.1, congrArg Subtype.val hx⟩

variable {S : Scheme.{0}}

theorem comp_act_natCast (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h0 : t.act.act 0 = 1 := by
      have h : t.act.act 0 * t.act.act 0 = t.act.act 0 * 1 := by
        rw [_root_.mul_one, ← t.act.add, add_zero]
      exact mul_left_cancel h
    rw [Nat.cast_zero, h0, comp_one, _root_.pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, t.act.add, comp_mul, ih, t.act.one, Category.comp_id, _root_.pow_succ]

theorem card_preimage {Q Q' : Type} (r : Q → Q') (hr : Function.Injective r) (A : Set Q')
    (hA : ∀ y ∈ A, ∃ x, r x = y) : Nat.card (r ⁻¹' A) = Nat.card A := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨r x.1, x.2⟩) ⟨?_, ?_⟩
  · intro a b hab
    exact Subtype.ext (hr (congrArg Subtype.val hab))
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hA y hy
    exact ⟨⟨x, hy⟩, rfl⟩

theorem heckeKer_comap (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (t : SAB H S) {T T' : Over S} (e : T' ⟶ T)
    (r : (T ⟶ t.G) →* (T' ⟶ t.G)) (he : ∀ x, r x = e ≫ x) (hp : (p : 𝓞 E) ∈ P)
    (hr : Function.Injective r) (hs : ∀ y, y ^ (p ^ 2) = 1 → ∃ x, r x = y)
    (hw : ∀ x y, x ^ (p ^ 2) = 1 → y ^ (p ^ 2) = 1 → Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) (r x) (r y) 1 →
      Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) x y 1)
    (C : Subgroup (T' ⟶ t.G)) (hC : t.HeckeKer T' D P p i C) : t.HeckeKer T D P p i (C.comap r) := by
  have hcomm : ∀ (x : T ⟶ t.G) (a : 𝓞 E), r (x ≫ t.act.act a) = r x ≫ t.act.act a := by
    intro x a
    rw [he, he, Category.assoc]
  have htors : ∀ (J : Ideal (𝓞 E)) (x : T ⟶ t.G), x ∈ t.tors T J ↔ r x ∈ t.tors T' J := by
    intro J x
    simp only [SAB.tors, Set.mem_ofPred_eq]
    refine forall₂_congr fun a _ => ?_
    rw [← hcomm]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      apply hr
      rw [h, map_one]
  have hkill : ∀ (z : T' ⟶ t.G) (J : Ideal (𝓞 E)), (p : 𝓞 E) ^ 2 ∈ J → z ∈ t.tors T' J → z ^ (p ^ 2) = 1 := by
    intro z J hJ hz
    rw [← comp_act_natCast t z (p ^ 2), Nat.cast_pow]
    exact hz _ hJ
  have hsp : (p : 𝓞 E) ^ 2 ∈ Ideal.span {(p : 𝓞 E)} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self _ two_ne_zero)
  have hmem : (p : 𝓞 E) ^ 2 ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [sq]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp
  have hpow : ∀ x : T ⟶ t.G, r x ^ (p ^ 2) = 1 → x ^ (p ^ 2) = 1 := by
    intro x h
    apply hr
    rw [map_pow, h, map_one]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx a
    rw [Subgroup.mem_comap, hcomm]
    exact c1 _ hx a
  · intro J hJ x hx
    exact c2 J hJ ((htors J x).1 hx)
  · intro x hx
    exact (htors _ x).2 (c3 hx)
  · intro x hx y hy
    exact hw x y (hpow x (hkill _ _ hmem (c3 hx))) (hpow y (hkill _ _ hmem (c3 hy))) (c4 _ hx _ hy)
  · rw [← c5]
    exact card_preimage r hr (C : Set (T' ⟶ t.G)) (fun y hy => hs y (hkill y _ hmem (c3 hy)))
  · have e1 : t.tors T (Ideal.span {(p : 𝓞 E)}) = r ⁻¹' t.tors T' (Ideal.span {(p : 𝓞 E)}) :=
      Set.ext fun x => htors _ x
    have e2 : (C.comap r : Set (T ⟶ t.G)) ∩ t.tors T (Ideal.span {(p : 𝓞 E)}) =
        r ⁻¹' ((C : Set (T' ⟶ t.G)) ∩ t.tors T' (Ideal.span {(p : 𝓞 E)})) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap]
      rw [htors]
    rw [e2, e1, card_preimage r hr _ (fun y hy => hs y (hkill y _ hsp hy)),
      card_preimage r hr _ (fun y hy => hs y (hkill y _ hsp hy.2))]
    exact c6

end GlobalTheory.HkSetDesc

open GlobalTheory.HkSetDesc in

theorem GlobalTheory.heckeSet_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) (o' : Ob D l s') (m : ObjMap o' o f) (K : Set o.t.G.left), admitted l 𝔓 p → Surjective f → HeckeSet D o'.t 𝔓 p i (m.toSABMap.φ ⁻¹' K) → HeckeSet D o.t 𝔓 p i K := by
  intro E _ _ _ H D l 𝔓 p i S S' s s' f o o' m K hA hf hK k _ _ x
  obtain ⟨k', _, _, β, x', hx'⟩ := exists_lift f x
  have hxs : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage (x ≫ s)).symm
  obtain ⟨-, I, -⟩ := o.geom k x _ hxs
  have hxs' : (x' ≫ f) ≫ s = spMap (Spec.preimage ((x' ≫ f) ≫ s)).hom := (Spec.map_preimage _).symm
  obtain ⟨-, I', -⟩ := o.geom k' (x' ≫ f) _ hxs'
  have hn : 0 < p ^ 2 := pow_pos hA.2.2.1.pos 2
  let e : Over.mk (x' ≫ f) ⟶ Over.mk x := Over.homMk (spMap β) hx'.symm
  have hepi : Epi (spMap β) := Flat.epi_of_flat_of_surjective (spMap β)
  let r : (Over.mk x ⟶ o.t.G) →* (Over.mk (x' ≫ f) ⟶ o.t.G) :=
    { toFun := fun z => e ≫ z
      map_one' := comp_one e
      map_mul' := fun a b => comp_mul e a b }
  have hr : Function.Injective r := by
    intro a b hab
    apply Over.OverMorphism.ext
    apply (cancel_epi (spMap β)).1
    exact congrArg (fun z => CommaMorphism.left z) hab
  have hs : ∀ y : Over.mk (x' ≫ f) ⟶ o.t.G, y ^ (p ^ 2) = 1 → ∃ z, r z = y :=
    fun y hy => torsion_onto I I' r hr hn y hy
  have hAb : IsAbelianScheme o.t.G := by
    constructor
    all_goals first
      | exact inferInstance
      | exact o.proper
      | exact o.t.comm
      | exact o.t.semi.smooth
      | exact o.t.semi.geomConnected
  have hinj : Function.Injective (Units.map e.left.appTop.hom.toMonoidHom) := by
    apply Units.map_injective
    show Function.Injective (Spec.map (CommRingCat.ofHom β)).appTop.hom
    intro a b hab
    have key := congrArg (fun g => g.hom) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom β))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at key
    have h1 := RingHom.congr_fun key a
    have h2 := RingHom.congr_fun key b
    simp only [RingHom.comp_apply] at h1 h2
    rw [hab, h2] at h1
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β.injective h1)
    simpa using h3.symm
  have hw : ∀ (a b : Over.mk x ⟶ o.t.G), a ^ (p ^ 2) = 1 → b ^ (p ^ 2) = 1 →
      Out.WeilIs o.t.G o.t.PP.L ((p : ℤ) ^ 2) (r a) (r b) 1 →
      Out.WeilIs o.t.G o.t.PP.L ((p : ℤ) ^ 2) a b 1 := by
    intro a b ha hb hab
    obtain ⟨u, rfl⟩ := (I.onto _ hn a).1 ha
    obtain ⟨v, rfl⟩ := (I.onto _ hn b).1 hb
    have h1 := I.isom _ hn u v
    have hpp : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by push_cast; rfl
    simp only [hpp] at h1
    have h2 := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hAb o.t.PP.isLB e h1
    have h3 := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hAb o.t.PP.isLB h2 hab
    rw [hinj (h3.trans (map_one _).symm)] at h1
    exact h1
  obtain ⟨C', hC'K, hC'⟩ := hK k' x'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HkSetPull.exists_equiv m.toSABMap.cart (Over.mk x')
  let C2 : Subgroup (Over.mk (x' ≫ f) ⟶ o.t.G) := C'.map ρ.toMonoidHom
  have hC2 : o.t.HeckeKer (Over.mk (x' ≫ f)) D 𝔓 p i C2 := by
    refine (GlobalTheory.HkSetPull.heckeKer_iff D 𝔓 p i m.toSABMap (Over.mk x') C' C2 ?_).1 hC'
    intro u v huv
    have hv : v = ρ u := Over.OverMorphism.ext (by rw [hρ]; exact huv)
    rw [hv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  refine ⟨C2.comap r, ?_, heckeKer_comap D 𝔓 p i o.t e r (fun _ => rfl) hA.2.2.2.1 hr hs hw C2 hC2⟩
  intro z
  rw [Subgroup.mem_comap, Subgroup.mem_map_equiv, hC'K]
  have hu := hρ (ρ.symm (r z))
  rw [MulEquiv.apply_symm_apply] at hu
  simp only [Set.range_subset_iff, Set.mem_preimage]
  constructor
  · intro h w
    obtain ⟨y, rfl⟩ := Surjective.surj (f := spMap β) w
    have := h y
    rw [← Scheme.Hom.comp_apply, ← hu] at this
    exact this
  · intro h y
    rw [← Scheme.Hom.comp_apply, ← hu]
    exact h _
