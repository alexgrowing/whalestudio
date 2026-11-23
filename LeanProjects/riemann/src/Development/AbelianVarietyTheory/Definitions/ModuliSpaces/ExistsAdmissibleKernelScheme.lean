import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliNonemptyPositiveDim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPrimeOutsideLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.HkFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {S : Scheme.{0}} {s : S ⟶ Sp (KA l)}

namespace IndexZero
open GlobalTheory.HeckeKerModel

theorem pointwise_iff : ToroidalHeckeCompatibility (H := H) (D := D) ↔ ∀ (l : Level H) (Xo : Moduli D l) (P : Ideal (𝓞 E)) (p i : ℕ),
    admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)),
      Xo.univ.t.HeckeKer (Over.mk y) D P p i C → ∃! y'', PointQuot Xo p y y'' C :=
  ⟨fun h l Xo P p i ⟨a, b, c, d, e⟩ => h l Xo P p i a b c d e,
    fun h l Xo P p i a b c d e => h l Xo P p i ⟨a, b, c, d, e⟩⟩

theorem exists_pt (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X), Set.range x = {g} := by
  refine ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g))))
      ≫ X.fromSpecResidueField g, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨IsLocalRing.closedPoint _, ?_⟩, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

theorem lift_closed {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have hs : Surjective (pullback.snd ν x) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
  have : IsIso (pullback.snd ν x) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem set_ext {G : Over S} {K K' : Set G.left}
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G),
      Set.range z.left ⊆ K ↔ Set.range z.left ⊆ K') : K = K' := by
  ext g
  obtain ⟨k, _, _, z, hz⟩ := exists_pt G.left g
  have := h k (z ≫ G.hom) (Over.homMk z rfl)
  change Set.range z ⊆ K ↔ Set.range z ⊆ K' at this
  simpa [hz] using this

theorem kerSet_unique {G G' : Over S} [GrpObj G'] {ψ : G ⟶ G'} {K K' : Set G.left} (h : KerSet ψ K)
    (h' : KerSet ψ K') : K = K' :=
  set_ext fun k _ _ x z => (h k x z).symm.trans (h' k x z)

theorem kerSet_preimage {G G' : Over S} [GrpObj G'] [IsSeparated G'.hom] (ψ : G ⟶ G') :
    KerSet ψ (ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
  intro k _ _ x z
  have hw : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by rw [hw]; infer_instance
    exact IsClosedImmersion.of_comp _ G'.hom
  have h1 : (1 : Over.mk x ⟶ G').left = x ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := rfl
  constructor
  · rintro h _ ⟨w, rfl⟩
    refine ⟨x w, ?_⟩
    have := congrArg (fun f : Over.mk x ⟶ G' => f.left w) h
    simp only [h1, Over.comp_left, Scheme.Hom.comp_apply] at this
    exact this.symm
  · intro h
    obtain ⟨t, ht⟩ := lift_closed (T := Sp k) (z.left ≫ ψ.left) (η[G'] : 𝟙_ (Over S) ⟶ G').left (by
      rintro _ ⟨w, rfl⟩
      exact h ⟨w, rfl⟩)
    have ht' : t = x := by
      have := Over.w (z ≫ ψ)
      rw [Over.comp_left, ← ht, Category.assoc, hw] at this
      exact (Category.comp_id _).symm.trans this
    exact Over.OverMorphism.ext (by rw [h1, Over.comp_left, ← ht, ht'])

theorem etSet_of_kerSet {G G' : Over S} [GrpObj G'] [IsSeparated G'.hom] {ψ : G ⟶ G'} [IsFinite ψ.left] [Etale ψ.left]
    {K : Set G.left} (h : KerSet ψ K) : EtSet G K := by
  have hw : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by rw [hw]; infer_instance
    exact IsClosedImmersion.of_comp _ G'.hom
  refine ⟨Over.mk (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left),
    Over.homMk (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Over.w ψ, ← Category.assoc, pullback.condition, Category.assoc, hw]
    exact Category.comp_id _
  · exact inferInstanceAs (IsFinite (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left))
  · exact inferInstanceAs (Etale (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left))
  · exact inferInstanceAs (IsClosedImmersion (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left))
  · rw [kerSet_unique h (kerSet_preimage ψ)]
    exact Scheme.Pullback.range_fst _ _

theorem isHecke_iff (o o' : Ob D l s) (P : Ideal (𝓞 E)) (p i : ℕ) (ψ : o.t.G ⟶ o'.t.G) :
    IsHecke o o' P p i ψ ↔ IsIsog o o' p ψ ∧ ∃ K, KerSet ψ K ∧ HeckeSet D o.t P p i K ∧ EtSet o.t.G K ∧ HasQuot o p K := by
  refine ⟨fun ⟨h, K, hK, hH⟩ => ⟨h, K, hK, hH, ?_, o', ψ, h, hK⟩, fun ⟨h, K, hK, hH, _⟩ => ⟨h, K, hK, hH⟩⟩
  have := o'.proper
  have := h.1.2.1
  have := h.1.2.2.1
  exact etSet_of_kerSet hK

def torsSet (o : Ob D l s) (p : ℕ) : Set o.t.G.left :=
  (o.t.act.act (p : 𝓞 E)).left ⁻¹' Set.range (η[o.t.G] : 𝟙_ (Over S) ⟶ o.t.G).left

theorem range_subset_torsSet (o : Ob D l s) (p : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (z : Over.mk x ⟶ o.t.G) : Set.range z.left ⊆ torsSet o p ↔ z ≫ o.t.act.act (p : 𝓞 E) = 1 := by
  have := o.proper
  exact (kerSet_preimage _ k x z).symm

theorem heckeKer_tors (o : Ob D l s) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) : o.t.HeckeKer (Over.mk x) D P p 0 (torsSub o.t (Over.mk x) p) :=
  heckeKer_zero o k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm P p hp

theorem heckeSet_torsSet (o : Ob D l s) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) :
    HeckeSet D o.t P p 0 (torsSet o p) := fun k _ _ x =>
  ⟨_, fun z => by rw [range_subset_torsSet, comp_act_natCast]; exact mem_tors_span o.t z p,
    heckeKer_tors o P hp k x⟩

theorem eq_torsSub (o : Ob D l s) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (C : Subgroup (Over.mk x ⟶ o.t.G)) (hC : o.t.HeckeKer (Over.mk x) D P p 0 C) :
    C = torsSub o.t (Over.mk x) p := by
  have hT := (heckeKer_tors o P hp k x).2.2.2.2.1
  have h1 := hC.2.2.2.2.1
  have h2 := hC.2.2.2.2.2
  rw [pow_zero, _root_.mul_one] at h2
  have fT : Finite (torsSub o.t (Over.mk x) p) := Nat.finite_of_card_ne_zero (hT ▸ pow_ne_zero _ hp.ne')
  have fC : Finite C := Nat.finite_of_card_ne_zero (h1 ▸ pow_ne_zero _ hp.ne')
  have e1 : C ⊓ torsSub o.t (Over.mk x) p = torsSub o.t (Over.mk x) p :=
    Subgroup.eq_of_le_of_card_ge inf_le_right h2.le
  exact (Subgroup.eq_of_le_of_card_ge (e1 ▸ inf_le_left) (h1.trans hT.symm).le).symm

theorem eq_torsSet (o : Ob D l s) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) {K : Set o.t.G.left}
    (hK : HeckeSet D o.t P p 0 K) : K = torsSet o p :=
  set_ext fun k _ _ x z => by
    obtain ⟨C, hC, hk⟩ := hK k x
    rw [← hC, eq_torsSub o P hp k x C hk, range_subset_torsSet, comp_act_natCast]
    exact mem_tors_span o.t z p

theorem torsSet_pull {S' : Scheme.{0}} {s' : S' ⟶ Sp (KA l)} (o' : Ob D l s') (o : Ob D l s) {f : S' ⟶ S}
    (n : ObjMap o' o f) (p : ℕ) : torsSet o' p = n.toSABMap.φ ⁻¹' torsSet o p :=
  set_ext fun k _ _ x z => by
    have hc := n.cart.1
    let z₀ : Over.mk (x ≫ f) ⟶ o.t.G := Over.homMk (z.left ≫ n.cm.F) (by
      rw [Category.assoc, hc.w, ← Category.assoc, Over.w z]; rfl)
    have e0 : Set.range z.left ⊆ n.toSABMap.φ ⁻¹' torsSet o p ↔ Set.range z₀.left ⊆ torsSet o p := by
      constructor
      · rintro h _ ⟨w, rfl⟩; exact h ⟨w, rfl⟩
      · rintro h _ ⟨w, rfl⟩; exact h ⟨w, rfl⟩
    have he : (η[o'.t.G] : 𝟙_ (Over S') ⟶ o'.t.G).left ≫ n.cm.F = f ≫ (η[o.t.G] : 𝟙_ (Over S) ⟶ o.t.G).left := by
      have := n.cm.e_comm
      rw [n.base] at this
      exact this
    have h1 : (1 : Over.mk x ⟶ o'.t.G).left ≫ n.cm.F = (1 : Over.mk (x ≫ f) ⟶ o.t.G).left :=
      ((Category.assoc x _ _).trans (congrArg (x ≫ ·) he)).trans (Category.assoc x f _).symm
    have h2 : (z ≫ o'.t.act.act (p : 𝓞 E)).left ≫ n.cm.F = (z₀ ≫ o.t.act.act (p : 𝓞 E)).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, n.act]
      exact (Category.assoc _ _ _).symm
    rw [e0, range_subset_torsSet, range_subset_torsSet]
    constructor
    · intro h
      exact Over.OverMorphism.ext (by rw [← h2, h, h1])
    · intro h
      refine Over.OverMorphism.ext (hc.hom_ext (by rw [h2, h, h1]) ?_)
      rw [Over.w, Over.w]

theorem isHecke_mul [IsLocallyNoetherian S] (o : Ob D l s) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) : IsHecke o o P p 0 (o.t.act.act (p : 𝓞 E)) := by
  have hg := (GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ S s o).2.1
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  let Q := HeckePoint.polOf o.t o.proper o.ample o.ktriv hg
  have e : o.t.act.act (p : 𝓞 E) = 𝟙 o.t.G ^ p := by rw [← comp_act_natCast, Category.id_comp]
  obtain ⟨h1, -, h2, h3, -⟩ := hL.mulN S Q p hp
  have hu : IsUnit (p : Γ(S, ⊤)) := by
    have h0 : IsUnit (p : Γ(Sp (KA l), ⊤)) := by
      simpa using ((baseKA l).unit p hp).map (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom
    simpa using h0.map s.appTop.hom
  have := o.proper
  refine ⟨⟨⟨o.t.act.hom _, e ▸ h1, e ▸ h3 hu, e ▸ h2, fun a => ?_, ?_⟩, fun p' hp' a => ?_⟩, _, kerSet_preimage _,
    heckeSet_torsSet o P hp⟩
  · rw [← o.t.act.mul, ← o.t.act.mul, _root_.mul_comm]
  · have hN := o.t.PP.isLB
    have h₂ := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hN _ _)).2 (hL.mulPull S Q p)
    rw [CechPic.cls_linComb hN] at h₂
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, CechPic.pull_id, one_zsmul,
      neg_zsmul] at h₂
    refine (CechPic.cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hN _ _)).1 ?_
    rw [CechPic.cls_lbPow hN, CechPic.cls_pull hN, e, ← add_neg_eq_zero.1 h₂, ← natCast_zsmul, Nat.cast_pow]
    exact congrArg _ (CechPic.pull_id _).symm
  · have key : ∀ f : D.La → (𝟙_ (Over S) ⟶ o.t.G), (∀ a c, f (a + c) = f a * f c) → ∀ (n : ℕ) a, f a ^ n = f (n • a) := by
      intro f hf n a
      induction n with
      | zero =>
        have h := hf 0 0
        rw [add_zero] at h
        rw [pow_zero, zero_nsmul, left_eq_mul.1 h]
      | succ n ih => rw [pow_succ, ih, succ_nsmul, hf]
    have hM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul (HeckePoint.natCast_M_mem l) Submodule.mem_top)
    rw [comp_act_natCast, comp_act_natCast, key _ o.eta_add, key _ o.etaA_add, ← mul_nsmul',
      HeckePoint.eq_of_modEq _ o.eta_add hM (hp'.of_dvd (Nat.dvd_lcm_left _ _)),
      HeckePoint.eq_of_modEq _ o.etaA_add o.etaA_ker (hp'.of_dvd (Nat.dvd_lcm_right _ _)), one_nsmul]
    exact ⟨rfl, rfl⟩

theorem etSet_torsSet [IsLocallyNoetherian S] (o : Ob D l s) {p : ℕ} (hp : 0 < p) : EtSet o.t.G (torsSet o p) := by
  obtain ⟨-, K, -, h1, h2, -⟩ := (isHecke_iff o o ⊤ p 0 _).1 (isHecke_mul o ⊤ hp)
  exact eq_torsSet o ⊤ hp h1 ▸ h2

def univId (Xo : Moduli D l) : Ob D l (𝟙 Xo.X ≫ Xo.s) :=
  { Xo.univ with geom := fun k _ _ x β hx => Xo.univ.geom k x β (by rw [← hx, Category.id_comp]) }

def kerZero (Xo : Moduli D l) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) : KerScheme Xo P p 0 where
  Hk := Xo.X
  π₁ := 𝟙 _
  fin₁ := inferInstance
  et₁ := inferInstance
  o₁ := univId Xo
  m₁ := ⟨ObjComp.sabMapId Xo.univ.t, (ObjComp.objMapId Xo.univ).eta, (ObjComp.objMapId Xo.univ).etaA⟩
  K := torsSet (univId Xo) p
  hecke := heckeSet_torsSet _ P hp
  et := by
    have := Xo.smooth
    have := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth D.dim Xo.s)).2.2
    exact etSet_torsSet (univId Xo) hp
  rep := fun S s hS o K' _ hK => by
    obtain ⟨f, ⟨hf, ⟨n⟩⟩, hu⟩ := Xo.rep S s hS o
    let n' : ObjMap o (univId Xo) f := ⟨n.toSABMap, n.eta, n.etaA⟩
    refine ⟨f, ⟨by rw [Category.id_comp, hf], n', (eq_torsSet o P hp hK).trans (torsSet_pull o _ n' p)⟩, ?_⟩
    rintro g ⟨hg, m, -⟩
    exact hu g ⟨by rw [← hg, Category.id_comp], ⟨⟨m.toSABMap, m.eta, m.etaA⟩⟩⟩

theorem kerZero_carries (Xo : Moduli D l) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) (k : Type) [Field k] [IsAlgClosed k]
    (y : Sp k ⟶ Xo.X) : (kerZero Xo P hp).Carries y y (torsSub Xo.univ.t (Over.mk y) p) := by
  refine ⟨Category.comp_id _, fun u v huv => ?_⟩
  have : v = u := Over.OverMorphism.ext (huv.trans (Category.comp_id _))
  subst this
  refine (range_subset_torsSet (univId Xo) p k y v).trans ?_
  exact (comp_act_natCast Xo.univ.t v p ▸ (mem_tors_span Xo.univ.t v p).symm :
    v ≫ Xo.univ.t.act.act (p : 𝓞 E) = 1 ↔ _)

theorem exists_kerScheme (hr : 1 ≤ D.p + D.q) (l : Level H) (P : Ideal (𝓞 E)) {p : ℕ} (hp : 0 < p) :
    ∃ (Xo : Moduli D l) (Z : KerScheme Xo P p 0) (z : Sp ℂ ⟶ Z.Hk) (y : Sp ℂ ⟶ Xo.X)
      (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)),
      Z.Carries z y C ∧ Nat.card C = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := by
  obtain ⟨Xo, y, -⟩ := ModuliInhabitant.moduli_inhabited.1 E H D hr l
  exact ⟨Xo, kerZero Xo P hp, y, y, _, kerZero_carries Xo P hp ℂ y, (heckeKer_tors Xo.univ P hp ℂ y).2.2.2.2.1⟩

theorem exists_adm (l : Level H) : ∃ (P : Ideal (𝓞 E)) (p : ℕ), admitted l P p :=
  GlobalTheory.exists_split_prime_outside_level E H l

theorem exists_admissible_kernel_scheme (hr : 1 ≤ D.p + D.q) (l : Level H) :
    ∃ (P : Ideal (𝓞 E)) (p : ℕ) (Xo : Moduli D l) (Z : KerScheme Xo P p 0) (z : Sp ℂ ⟶ Z.Hk) (y : Sp ℂ ⟶ Xo.X)
      (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), admitted l P p ∧ Z.Carries z y C ∧ C ≠ ⊥ := by
  obtain ⟨P, p, h⟩ := exists_adm l
  obtain ⟨Xo, Z, z, y, C, h1, h2⟩ := exists_kerScheme hr l P h.2.2.1.pos
  refine ⟨P, p, Xo, Z, z, y, C, h, h1, fun hC => ?_⟩
  rw [hC, Subgroup.card_bot] at h2
  have h3 : 2 ≤ Module.finrank ℚ E := by
    have := NumberField.IsTotallyComplex.finrank E
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have h4 : 0 < Module.finrank ℚ E / 2 * (D.p + D.q) := Nat.mul_pos (by omega) hr
  exact (Nat.one_lt_pow (by omega) h.2.2.1.one_lt).ne h2

end IndexZero

namespace KerScheme
variable {Xo : Moduli D l} {𝔓 : Ideal (𝓞 E)} {p i : ℕ}

theorem smooth (Z : KerScheme Xo 𝔓 p i) : Smooth (Z.π₁ ≫ Xo.s) := by
  have := Xo.smooth
  have := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := Z.et₁
  infer_instance

theorem isReduced (Z : KerScheme Xo 𝔓 p i) : IsReduced Z.Hk :=
  (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ Z.smooth).1

theorem comp_π₁ (Z : KerScheme Xo 𝔓 p i) [IsReduced S] {o : Ob D l s} {h : S ⟶ Z.Hk} (hh : h ≫ Z.π₁ ≫ Xo.s = s)
    (n : ObjMap o Z.o₁ h) {f : S ⟶ Xo.X} (hf : f ≫ Xo.s = s) (m : ObjMap o Xo.univ f) : h ≫ Z.π₁ = f := by
  obtain ⟨m', -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₁ o).2 Z.π₁ h Z.m₁).1 n
  exact (Xo.rep S s inferInstance o).unique ⟨by rw [Category.assoc, hh], ⟨m'⟩⟩ ⟨hf, ⟨m⟩⟩

theorem exists_iso (Z Z' : KerScheme Xo 𝔓 p i) :
    ∃ e : Z.Hk ≅ Z'.Hk, e.hom ≫ Z'.π₁ = Z.π₁ ∧ ∃ n : ObjMap Z.o₁ Z'.o₁ e.hom, Z.K = n.toSABMap.φ ⁻¹' Z'.K := by
  have key : ∀ (Z Z' : KerScheme Xo 𝔓 p i) (h : Z.Hk ⟶ Z'.Hk) (h' : Z'.Hk ⟶ Z.Hk),
      h ≫ Z'.π₁ ≫ Xo.s = Z.π₁ ≫ Xo.s → h' ≫ Z.π₁ ≫ Xo.s = Z'.π₁ ≫ Xo.s → ∀ (n : ObjMap Z.o₁ Z'.o₁ h) (n' : ObjMap Z'.o₁ Z.o₁ h'),
      Z.K = n.toSABMap.φ ⁻¹' Z'.K → Z'.K = n'.toSABMap.φ ⁻¹' Z.K → h ≫ h' = 𝟙 _ := by
    intro Z Z' h h' e e' n n' hK hK'
    obtain ⟨⟨m₀, hm₀⟩, -⟩ := GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z.o₁ Z.o₁
    obtain ⟨m, hm⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z'.o₁ Z.o₁).2 h' h n').1 n
    refine (Z.rep _ _ Z.isReduced Z.o₁ Z.K Z.et Z.hecke).unique ⟨by rw [Category.assoc, e', e], m, ?_⟩
      ⟨Category.id_comp _, m₀, by rw [hm₀]; rfl⟩
    rw [hm, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← hK', ← hK]
  obtain ⟨h, ⟨e, n, hK⟩, -⟩ := Z'.rep _ _ Z.isReduced Z.o₁ Z.K Z.et Z.hecke
  obtain ⟨h', ⟨e', n', hK'⟩, -⟩ := Z.rep _ _ Z'.isReduced Z'.o₁ Z'.K Z'.et Z'.hecke
  have := Z.isReduced
  exact ⟨⟨h, h', key Z Z' h h' e e' n n' hK hK', key Z' Z h' h e' e n' n hK' hK⟩,
    Z'.comp_π₁ e n rfl Z.m₁, n, hK⟩

end KerScheme

example {Xo : Moduli D l} {𝔓 : Ideal (𝓞 E)} {p : ℕ} (hp : 0 < p) (Z : KerScheme Xo 𝔓 p 0) : IsIso Z.π₁ := by
  obtain ⟨e, he, -⟩ := Z.exists_iso (IndexZero.kerZero Xo 𝔓 hp)
  have : e.hom = Z.π₁ := (Category.comp_id _).symm.trans he
  exact this ▸ e.isIso_hom

end GlobalTheory.HkFam
end
