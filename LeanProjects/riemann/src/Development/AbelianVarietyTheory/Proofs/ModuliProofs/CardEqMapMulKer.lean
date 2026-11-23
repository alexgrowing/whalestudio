import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HeckeDual

open GlobalTheory.HeckeKerModel

section Count

theorem card_eq_map_mul_ker {A B : Type} [Group A] [Group B] (f : A →* B) (X : Subgroup A) (h : f.ker ≤ X) :
    Nat.card X = Nat.card (X.map f) * Nat.card f.ker := by
  have h1 := (f.domRestrict X).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  rw [← h1, Nat.mul_comm]

theorem card_dual_ker {Q Q' : Type} [CommGroup Q] [CommGroup Q'] (f : Q →* Q') (g : Q' →* Q) (p N : ℕ)
    (hf : Function.Surjective f) (hg : ∀ x, g (f x) = x ^ p ^ 2) (hN : N ≠ 0)
    (h1 : Nat.card (powMonoidHom p : Q →* Q).ker = N) (h2 : Nat.card (powMonoidHom (p ^ 2) : Q →* Q).ker = N ^ 2)
    (h3 : Nat.card f.ker = N) (hdiv : ∀ x : Q, x ^ p = 1 → ∃ y, y ^ p = x) :
    Nat.card g.ker = N ∧ Nat.card (g.ker ⊓ (powMonoidHom p : Q' →* Q').ker : Subgroup Q') =
      Nat.card (f.ker ⊓ (powMonoidHom p : Q →* Q).ker : Subgroup Q) := by
  have hle : ∀ x, f x = 1 → x ^ p ^ 2 = 1 := fun x hx => by rw [← hg, hx, map_one]
  constructor
  · have e := card_eq_map_mul_ker f (powMonoidHom (p ^ 2) : Q →* Q).ker hle
    have e' : (powMonoidHom (p ^ 2) : Q →* Q).ker.map f = g.ker := by
      ext y
      obtain ⟨x, rfl⟩ := hf y
      refine ⟨?_, fun h => ⟨x, (hg x).symm.trans h, rfl⟩⟩
      rintro ⟨z, hz, ez⟩
      rw [← ez]
      exact (hg z).trans hz
    rw [e', h2, h3, sq] at e
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN) e).symm
  · let X : Subgroup Q := (f.ker ⊓ (powMonoidHom p : Q →* Q).ker).comap (powMonoidHom p)
    have hX : ∀ x, x ∈ X ↔ f x ^ p = 1 ∧ x ^ p ^ 2 = 1 := fun x => by
      rw [← map_pow, sq, pow_mul]
      rfl
    have e := card_eq_map_mul_ker f X fun x hx => (hX x).2 ⟨by rw [show f x = 1 from hx, one_pow], hle x hx⟩
    have e₂ := card_eq_map_mul_ker (powMonoidHom p) X fun x hx => (hX x).2 (by
      have hx' : x ^ p = 1 := hx
      rw [← map_pow, sq, pow_mul, hx', map_one, one_pow]
      exact ⟨rfl, rfl⟩)
    have e' : X.map f = g.ker ⊓ (powMonoidHom p : Q' →* Q').ker := by
      ext y
      obtain ⟨x, rfl⟩ := hf y
      refine ⟨?_, fun h => ⟨x, (hX x).2 ⟨h.2, (hg x).symm.trans h.1⟩, rfl⟩⟩
      rintro ⟨z, hz, ez⟩
      rw [← ez]
      exact ⟨(hg z).trans ((hX z).1 hz).2, ((hX z).1 hz).1⟩
    have e₂' : X.map (powMonoidHom p) = f.ker ⊓ (powMonoidHom p : Q →* Q).ker := by
      refine Subgroup.map_comap_eq_self fun x hx => hdiv x hx.2
    rw [e', h3] at e
    rw [e₂', h1] at e₂
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN) (e.symm.trans e₂)

end Count

variable {S : Scheme.{0}}

theorem exists_lift {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left] {k : Type} [Field k]
    [IsAlgClosed k] (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (IsLocalRing.closedPoint k)
  have : JacobsonSpace ↥(pullback ψ.left y') := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ.left y')
  obtain ⟨z', -, hz'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback ψ.left y')))
    ⟨z, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {z'} := hz'
  have e : (pointOfClosedPoint (pullback.snd ψ.left y') z' hc ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  exact ⟨Over.homMk (pointOfClosedPoint (pullback.snd ψ.left y') z' hc ≫ pullback.fst ψ.left y')
    (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y), Over.OverMorphism.ext e⟩

theorem kerSet_unit {G G' : Over S} [GrpObj G'] [IsSeparated G'.hom] (ψ : G ⟶ G') :
    KerSet ψ (ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
  intro k _ _ x z
  have hw : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by rw [hw]; infer_instance
    exact IsClosedImmersion.of_comp _ G'.hom
  have h1 : (1 : Over.mk x ⟶ G').left = x ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := rfl
  have lift_closed : ∀ {N B : Scheme.{0}} (u : Sp k ⟶ B) (ν : N ⟶ B) [IsClosedImmersion ν],
      Set.range u ⊆ Set.range ν → ∃ l : Sp k ⟶ N, l ≫ ν = u := fun u ν _ h => by
    have hs : Surjective (pullback.snd ν u) := ⟨by
      rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
      exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
    have : IsIso (pullback.snd ν u) := isIso_of_isClosedImmersion_of_surjective _
    exact ⟨inv (pullback.snd ν u) ≫ pullback.fst ν u, by
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩
  constructor
  · rintro h _ ⟨w, rfl⟩
    refine ⟨x w, ?_⟩
    have := congrArg (fun f : Over.mk x ⟶ G' => f.left w) h
    simp only [h1, Over.comp_left, Scheme.Hom.comp_apply] at this
    exact this.symm
  · intro h
    obtain ⟨t, ht⟩ := lift_closed (z.left ≫ ψ.left) (η[G'] : 𝟙_ (Over S) ⟶ G').left (by
      rintro _ ⟨w, rfl⟩
      exact h ⟨w, rfl⟩)
    have ht' : t = x := by
      have := Over.w (z ≫ ψ)
      rw [Over.comp_left, ← ht, Category.assoc, hw] at this
      exact (Category.comp_id _).symm.trans this
    exact Over.OverMorphism.ext (by rw [h1, Over.comp_left, ← ht, ht'])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem map_bar_map_bar (I : Ideal (𝓞 E)) :
    (I.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) = I := by
  have : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    change ((H.bar (H.bar a) : 𝓞 E) : E) = a
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  rw [Ideal.map_map, this, Ideal.map_id]

theorem absNorm_map_bar (I : Ideal (𝓞 E)) : Ideal.absNorm (I.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ H.bar rfl).toEquiv).symm

theorem mem_tors_mul (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (I J : Ideal (𝓞 E))
    (h : ∀ a ∈ I, x ≫ t.act.act a ∈ t.tors T J) : x ∈ t.tors T (I * J) := fun c hc =>
  Submodule.mul_induction_on hc
    (fun a ha b hb => by rw [t.act.mul, ← Category.assoc]; exact h a ha b hb)
    (fun a b ha hb => by rw [t.act.add, MonObj.comp_mul, ha, hb, _root_.one_mul])

theorem card_pow_ker {s : S ⟶ Sp (KA l)} (o : Ob D l s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    {n : ℕ} (hn : 0 < n) : Nat.card (o.t.tors (Over.mk x) (Ideal.span {(n : 𝓞 E)})) =
      n ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) :=
  (heckeKer_zero o k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm ⊤ n hn).2.2.2.2.1

end GlobalTheory.HeckeDual

namespace GlobalTheory

open HeckeDual HeckeKerModel

theorem isHecke_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G) (ψ' : o'.t.G ⟶ o.t.G), admitted l 𝔓 p → IsHecke o o' 𝔓 p i ψ → IsIsog o' o p ψ' → ψ ≫ ψ' = 𝟙 o.t.G ^ p ^ 2 → IsHecke o' o (𝔓.map (H.bar : 𝓞 E →+* 𝓞 E)) p i ψ' := by
  rintro E _ _ _ H D l P p i S s o o' ψ ψ' ⟨-, -, hp, hpP, -⟩ ⟨⟨⟨hm, hfin, -, hsurj, hlin, hLB⟩, -⟩, K, hK, hH⟩ h' hψ
  have hpr := o.proper
  have hm' := h'.1.1
  have hlin' := h'.1.2.2.2.2.1
  refine ⟨h', _, kerSet_unit ψ', fun k _ _ x => ?_⟩
  obtain ⟨C, hC, c1, c2, c3, -, c5, c6⟩ := hH k x
  let f : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ o'.t.G) := MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
  let g : (Over.mk x ⟶ o'.t.G) →* (Over.mk x ⟶ o.t.G) := MonoidHom.mk' (· ≫ ψ') fun a b => MonObj.mul_comp a b ψ'
  have hCf : C = f.ker := Subgroup.ext fun z => (hC z).trans (hK k x z).symm
  subst hCf
  have hf : Function.Surjective f := fun y => exists_lift ψ x y
  have hg : ∀ z, g (f z) = z ^ p ^ 2 := fun z => by
    change (z ≫ ψ) ≫ ψ' = _
    rw [Category.assoc, hψ, MonObj.comp_pow, Category.comp_id]
  have hfa : ∀ z a, f (z ≫ o.t.act.act a) = f z ≫ o'.t.act.act a := fun z a => by
    change (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
    rw [Category.assoc, hlin, Category.assoc]
  have hp0 := hp.pos
  have hq0 : 0 < p ^ 2 := pow_pos hp0 2
  have hsq : Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)} = Ideal.span {(p : 𝓞 E)} * Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, Nat.cast_pow, sq]
  obtain ⟨-, I, -⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm
  obtain ⟨-, I', -⟩ := o'.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm
  have tk : ∀ (u : Ob D l s) (n : ℕ), u.t.tors (Over.mk x) (Ideal.span {(n : 𝓞 E)}) =
      ((powMonoidHom n : (Over.mk x ⟶ u.t.G) →* (Over.mk x ⟶ u.t.G)).ker : Set _) := fun u n =>
    Set.ext fun z => mem_tors_span u.t z n
  obtain ⟨d5, d6⟩ := card_dual_ker f g p (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hf hg
    (pow_ne_zero _ hp0.ne') (by have := card_pow_ker o k x hp0; rw [tk] at this; exact this)
    (by have := card_pow_ker o k x hq0; rw [tk, ← pow_mul, Nat.mul_comm, pow_mul] at this; exact this) c5
    (fun z hz => by
      obtain ⟨a, rfl⟩ := (I.onto p hp0 z).1 hz
      exact ⟨_, I.tower p p hp0 hp0 a⟩)
  refine ⟨g.ker, fun z => kerSet_unit ψ' k x z, fun y hy a => ?_, fun J hJ y hy => ?_, fun y hy a ha => ?_,
    fun y hy y' hy' => ?_, d5, ?_⟩
  · have := o.t.act.hom a
    change (y ≫ _) ≫ ψ' = 1
    rw [Category.assoc, hlin', ← Category.assoc, show y ≫ ψ' = 1 from hy]
    simp
  · obtain ⟨z, rfl⟩ := hf y
    have h1 := mem_tors_mul o.t z J _ fun a ha => c3 (show f _ = 1 from (hfa z a).trans (hy a ha))
    rw [mul_left_comm, hJ, ← hsq, mem_tors_span] at h1
    exact (hg z).trans h1
  · obtain ⟨z, rfl⟩ := hf y
    have hz : z ∈ o.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)}) :=
      (mem_tors_span o.t z _).2 ((hg z).symm.trans hy)
    rw [map_bar_map_bar] at ha
    obtain ⟨J, hJ⟩ : P ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hpP)
    rw [← hfa]
    refine c2 J (by rw [hJ, _root_.mul_comm]) fun b hb => ?_
    rw [Category.assoc, ← o.t.act.mul]
    refine hz _ ?_
    have := Ideal.mul_mem_mul ha hb
    rwa [_root_.mul_assoc, ← hJ, ← hsq] at this
  · obtain ⟨z, rfl⟩ := hf y
    obtain ⟨z', rfl⟩ := hf y'
    have hz : z ^ p ^ 2 = 1 := (hg z).symm.trans hy
    have hz' : z' ^ p ^ 2 = 1 := (hg z').symm.trans hy'
    obtain ⟨a, ha⟩ := (I.onto _ hq0 z).1 hz
    obtain ⟨a', ha'⟩ := (I.onto _ hq0 z').1 hz'
    obtain ⟨b, hb⟩ := (I'.onto _ hq0 (f z)).1 (by rw [← map_pow, hz, map_one])
    obtain ⟨b', hb'⟩ := (I'.onto _ hq0 (f z')).1 (by rw [← map_pow, hz', map_one])
    have w := I.isom _ hq0 a a'
    have w' := I'.isom _ hq0 b b'
    rw [ha, ha'] at w
    rw [hb, hb'] at w'
    have e := (weilIs_along_hom firstFiveLaws.1.globalFns S _ _ ψ _ _ (p ^ 2) _ _ z z' _ _
      ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
      ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩ o.t.PP.isLB o'.t.PP.isLB hm hLB w').2 w
    have e1 : (unitOn (I.ζ (p ^ 2) ^ D.EF a a')) ^ p ^ 2 = 1 := by
      have h2 : (I.ζ (p ^ 2) ^ D.EF a a') ^ p ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, (I.ζ_prim _ hq0).pow_eq_one, one_zpow]
      exact (map_pow (Units.map _) _ _).symm.trans ((congrArg _ h2).trans (map_one _))
    have e2 : unitOn (I'.ζ (p ^ 2) ^ D.EF b b') = 1 := e.trans e1
    rw [e2] at w'
    exact_mod_cast w'
  · rw [absNorm_map_bar, card_pow_ker o' k x hp0, ← card_pow_ker o k x hp0, c6, tk, tk]
    exact congrArg (· * _) d6.symm

end GlobalTheory
