import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfPowEqInt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcInputCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Classes

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

def GtMod (_oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F] : Type := GtPtF D F

variable (hB : D.TauBimult) (oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F]

instance : AddCommGroup (GtMod oa F) := gtGroup D F

instance : Module O (GtMod oa F) := gtModule globalFns_holds oa F

def relMap (k : ℕ) : D.X →ₗ[O] D.X × GtMod oa F where
  toFun z := (k • z, iota hB F z)
  map_add' a b := Prod.ext (nsmul_add _ _ _) (map_add (iota hB F) a b)
  map_smul' a z := Prod.ext (smul_comm k a z) (iota_smul globalFns_holds oa hB a z)

variable {F} {k : ℕ}

def cls (p : QkPt D F k) : (D.X × GtMod oa F) ⧸ LinearMap.range (relMap hB oa F k) :=
  Submodule.Quotient.mk (p.y, p.g)

theorem equiv_iff_cls (p q : QkPt D F k) : QkPt.Equiv D F p q ↔ cls hB oa p = cls hB oa q := by
  rw [equiv_iff hB, cls, cls, eq_comm, Submodule.Quotient.eq]
  refine exists_congr fun z => ?_
  rw [eq_sub_iff_add_eq', Prod.ext_iff]
  exact and_congr eq_comm eq_comm

theorem add_iff_cls (p p' q : QkPt D F k) :
    Geo.Tor.QkAdd p p' q ↔ cls hB oa p + cls hB oa p' = cls hB oa q := by
  rw [TorusExt.qkAdd_iff hB, equiv_iff_cls hB oa]; rfl

theorem act_iff_cls (a : O) (p q : QkPt D F k) : QkAct oa a p q ↔ a • cls hB oa p = cls hB oa q := by
  rw [TorusExt.qkAct_iff hB globalFns_holds, equiv_iff_cls hB oa]; rfl

theorem zero_iff_equiv (p : QkPt D F k) : TateUniformizationInput.QkZero p ↔ QkPt.Equiv D F (qkZero hB F k) p := by
  rw [equiv_iff hB]
  refine exists_congr fun z => and_congr ?_ ?_
  · rw [qkZero, qkMk_y, zero_add]
  · rw [qkZero, qkMk_g, zero_add, isIota_iff_eq hB]

theorem zero_iff_cls (p : QkPt D F k) : TateUniformizationInput.QkZero p ↔ cls hB oa p = 0 := by
  rw [zero_iff_equiv hB, equiv_iff_cls hB oa, eq_comm]; rfl

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem equiv_iff_ext (p q : QkPt D F k) :
    QkPt.Equiv D F p q ↔ cls hB oa (qkExt hB f hf p) = cls hB oa (qkExt hB f hf q) := by
  rw [← equiv_iff_cls, ArcExt.equiv_qkExt_iff]

theorem add_iff_ext (p p' q : QkPt D F k) : TorusGraphMaps.QkAdd p p' q ↔
    cls hB oa (qkExt hB f hf p) + cls hB oa (qkExt hB f hf p') = cls hB oa (qkExt hB f hf q) := by
  rw [← DegActCompare.qkAdd_iff, TorusExt.qkAdd_iff hB, equiv_iff_ext hB oa f hf, qkExt_qkAdd]; rfl

theorem act_iff_ext (a : O) (p q : QkPt D F k) :
    TorusGraphMaps.QkSmul oa a p q ↔ a • cls hB oa (qkExt hB f hf p) = cls hB oa (qkExt hB f hf q) := by
  rw [← DegActCompare.qkAct_iff, TorusExt.qkAct_iff hB globalFns_holds, equiv_iff_ext hB oa f hf, qkExt_qkSmul]; rfl

theorem zero_iff_ext (p : QkPt D F k) : TateUniformizationInput.QkZero p ↔ cls hB oa (qkExt hB f hf p) = 0 := by
  have e : qkExt hB f hf (qkZero hB F k) = qkZero hB F' k := qk_ext rfl (map_zero (gtExt D f hf))
  rw [zero_iff_equiv hB, equiv_iff_ext hB oa f hf, e, eq_comm]; rfl

theorem isRatio_ext {p p' : QkPt D F k} {z : F} (h : QkPairing.IsRatio p p' z) :
    QkPairing.IsRatio (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  intro T σ y J hJ
  have e := h T (σ ≫ extMap f hf) y J hJ
  have v : ∀ (g : GtPtF D F) χ, val ((gtExt D f hf g).s χ) σ.left y J = val (g.s χ) (σ ≫ extMap f hf).left y J :=
    fun g χ => (val_corr hJ (((eq_gtExt_iff f hf g _).1 rfl).2 χ) _).trans (val_pull hJ _ _ _)
  have w : gs σ.left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (f z)) =
      gs (σ ≫ extMap f hf).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
    refine Eq.trans (congrArg (gs σ.left y ⊤) ?_) (gs_pull σ.left (spMap f) y ⊤ trivial _)
    exact congrArg (fun g => g.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [qkExt, qkMk_y, qkMk_g]
  rw [v, v, w, gtExt_b, gtExt_b, ← Category.assoc, ← Category.assoc]
  exact e

theorem weil_ext (k : ℕ) (hk : 1 ≤ k) (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  obtain ⟨u, hu⟩ := QkPairing.exists_ratio p p'
  obtain rfl := QkPairing.weil_unique globalFns_holds abelianSchemeLaws_all.2.secTwist hB hk p p' h
    (QkPairing.weil_of_ratio globalFns_holds p p' hu)
  exact QkPairing.weil_of_ratio globalFns_holds _ _ (ζ := Units.map f.toMonoidHom u) (isRatio_ext hB f hf hu)

end Classes

theorem injective_of_isAlgebraic {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [CharZero B]
    (h : ∀ x : A, IsAlgebraic ℤ x) (f : A →+* B) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun x hx => by_contra fun h0 => ?_
  refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker f) h0 hx (h x) (eq_bot_iff.2 fun n hn => ?_)
  have : f (n : A) = 0 := hn
  rw [map_intCast] at this
  exact Int.cast_eq_zero.1 this

theorem finrank_torusLieEigen {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] (k : Type) [Field k] [CharZero k] [Module.Finite ℤ X] (τ : 𝓞 E →+* k) :
    Module.finrank k (TateUniformizationInput.torusLieEigen H X k τ) = Module.finrank (𝓞 E) X := by
  let σ : 𝓞 E →+* k := τ.comp (H.bar : 𝓞 E →+* 𝓞 E)
  let _ := σ.toAlgebra
  have hσ : Function.Injective σ := injective_of_isAlgebraic (fun x => Algebra.IsAlgebraic.isAlgebraic x) σ
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hσ
  have : Module.Finite (𝓞 E) X := .of_restrictScalars_finite ℤ _ _
  let e : TateUniformizationInput.torusLieEigen H X k τ ≃ₗ[k] (X →ₗ[𝓞 E] k) :=
    { toFun := fun v => ⟨⟨v.1, map_add v.1⟩, fun a x => by
        have := v.2 (H.bar a) x
        rw [TorusGraphMaps.bar_bar] at this
        exact this⟩
      invFun := fun v => ⟨v.toAddMonoidHom, fun a x => by
        refine (v.map_smul _ _).trans ?_
        show τ (H.bar (H.bar a)) * _ = _
        rw [TorusGraphMaps.bar_bar]; rfl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, (LinearMap.liftBaseChangeEquiv k).finrank_eq]
  refine Subspace.dual_finrank_eq.trans ?_
  exact (TensorProduct.isBaseChange (𝓞 E) X k).finrank_eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]

open Classical in

theorem det_iff [CharZero F] (ρ : F) :
    (letI := H.starRing
      ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oa.onB.toRingAct)
        (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
        n + Module.finrank (𝓞 E) P.X = if τ H.rt = ρ then D.p else D.q) ↔ TateUniformizationInput.GtDetCond D oa F ρ := by
  have e : spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) = DegPre.jFR (R := R) F := by
    rw [DegPre.jFR, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine forall_congr' fun τ => ?_
  simp only [TateUniformizationInput.GtLieMult, finrank_torusLieEigen]
  rw [e]
  by_cases h : τ H.rt = ρ
  · rw [if_pos h]; exact ⟨fun k => ⟨fun _ => k, fun k' => absurd h k'⟩, fun k => k.1 h⟩
  · rw [if_neg h]; exact ⟨fun k => ⟨fun k' => absurd k' h, fun _ => k⟩, fun k => k.2 h⟩

variable (hB : P.TauBimult)

def toQTateIso (I : TateIsoQ D P oa F) : TateUniformizationInput.QTateIso D oa F where
  ζ n := I.ζ n
  ζ_prim n := I.ζ_prim n n.pos
  ζ_pow n m := I.ζ_pow n m n.pos m.pos
  ev n := I.ev n
  add n := I.add n n.pos
  lin n x a := letI := H.starRing; (DegActCompare.qkAct_iff oa x _ _).1 (I.lin n n.pos x a)
  ker n a := by
    letI := H.starRing
    have h := (add_iff_cls hB oa _ _ _).1 (I.add n n.pos 0 0)
    rw [add_zero, add_eq_left] at h
    rw [zero_iff_cls hB oa, ← h, ← equiv_iff_cls, I.ker n n.pos]
    simp only [zero_add]
  onto n := I.onto n n.pos
  tower n m a := ⟨rfl, I.tower n m n.pos m.pos a⟩
  isom n := I.isom n n.pos

def evNat (J : TateUniformizationInput.QTateIso D oa F) (n : ℕ) (a : D.La) : QkPt P F n :=
  if h : 0 < n then J.ev ⟨n, h⟩ a else qkZero hB F n

theorem evNat_pos (J : TateUniformizationInput.QTateIso D oa F) {n : ℕ} (h : 0 < n) : evNat hB J n = J.ev ⟨n, h⟩ :=
  funext fun _ => dif_pos h

include hB in
theorem equiv_ev_iff (J : TateUniformizationInput.QTateIso D oa F) (n : ℕ+) (a b : D.La) :
    QkPt.Equiv P F (J.ev n a) (J.ev n b) ↔ ∃ e, a = b + (n : ℕ) • e := by
  letI := H.starRing
  have k := (add_iff_cls hB oa _ _ _).1 (J.add n (a - b) b)
  rw [sub_add_cancel] at k
  rw [equiv_iff_cls hB oa, ← k, add_eq_right, ← zero_iff_cls, J.ker]
  exact exists_congr fun e => sub_eq_iff_eq_add'

def ofQTateIso (J : TateUniformizationInput.QTateIso D oa F) : TateIsoQ D P oa F where
  ζ n := if h : 0 < n then J.ζ ⟨n, h⟩ else 1
  ζ_prim n h := by rw [dif_pos h]; exact J.ζ_prim ⟨n, h⟩
  ζ_pow n m h h' := by rw [dif_pos h, dif_pos (Nat.mul_pos h h')]; exact J.ζ_pow ⟨n, h⟩ ⟨m, h'⟩
  ev := evNat hB J
  add n h := by rw [evNat_pos hB J h]; exact J.add ⟨n, h⟩
  lin n h x a := by
    letI := H.starRing
    rw [evNat_pos hB J h]; exact (DegActCompare.qkAct_iff oa x _ _).2 (J.lin ⟨n, h⟩ x a)
  ker n h a b := by rw [evNat_pos hB J h]; exact equiv_ev_iff hB J ⟨n, h⟩ a b
  onto n h := by rw [evNat_pos hB J h]; exact J.onto ⟨n, h⟩
  tower n m h h' a := by
    rw [evNat_pos hB J h, evNat_pos hB J (Nat.mul_pos h h')]; exact (J.tower ⟨n, h⟩ ⟨m, h'⟩ a).2
  isom n h := by rw [evNat_pos hB J h, dif_pos h]; exact J.isom ⟨n, h⟩

def SameIso (I : TateIsoQ D P oa F) (J : TateUniformizationInput.QTateIso D oa F) : Prop :=
  ∀ n : ℕ+, I.ζ n = J.ζ n ∧ I.ev n = J.ev n

theorem sameIso_to (I : TateIsoQ D P oa F) : SameIso I (toQTateIso hB I) := fun _ => ⟨rfl, rfl⟩

theorem sameIso_of (J : TateUniformizationInput.QTateIso D oa F) : SameIso (ofQTateIso hB J) J := fun n =>
  ⟨dif_pos n.pos, evNat_pos hB J n.pos⟩

def evLin (I : TateIsoQ D P oa F) {n : ℕ} (h : 0 < n) : letI := H.starRing
    D.La →ₗ[𝓞 E] (P.X × GtMod oa F) ⧸ LinearMap.range (relMap hB oa F n) :=
  letI := H.starRing
  { toFun := fun a => cls hB oa (I.ev n a)
    map_add' := fun a b => ((add_iff_cls hB oa _ _ _).1 (I.add n h a b)).symm
    map_smul' := fun x a => ((act_iff_cls hB oa _ _ _).1 (I.lin n h x a)).symm }

theorem evLin_eq_zero (I : TateIsoQ D P oa F) {n : ℕ} (h : 0 < n) (a : D.La) :
    evLin hB I h a = 0 ↔ ∃ e, a = n • e := by
  letI := H.starRing
  rw [← map_zero (evLin hB I h)]
  refine (equiv_iff_cls hB oa _ _).symm.trans ((I.ker n h a 0).trans ?_)
  simp only [zero_add]

theorem evLin_onto (I : TateIsoQ D P oa F) {n : ℕ} (h : 0 < n) (p : QkPt P F n) :
    ∃ a, evLin hB I h a = (letI := H.starRing; cls hB oa p) :=
  letI := H.starRing
  (I.onto n h p).imp fun _ k => (equiv_iff_cls hB oa _ _).1 k

end Data

section Lev

variable (D : Datum H) (l : Level H)

abbrev halfLat : Submodule (𝓞 E) D.La := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)

theorem mem_mul_iff (a : D.La) :
    a ∈ (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) ↔ ∃ e, a = l.M • e := by
  rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]
  exact exists_congr fun _ => eq_comm

theorem exists_split : ∃ m : 𝓞 E, m ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ 1 - m ∈ l.Mb := by
  obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ _)
  exact ⟨y, hy, by rw [← e, add_sub_cancel_right]; exact hx⟩

theorem smul_mem_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {I J : Ideal A} {m : A} (hm : m ∈ J)
    (hm' : 1 - m ∈ I) (a : M) : m • a ∈ (I * J) • (⊤ : Submodule A M) ↔ a ∈ I • (⊤ : Submodule A M) := by
  constructor
  · intro k
    have e := add_mem (Submodule.smul_mem_smul hm' (Submodule.mem_top (x := a)))
      (Submodule.smul_mono_left (Ideal.mul_le_inf.trans inf_le_left) k)
    rwa [← add_smul, sub_add_cancel, one_smul] at e
  · intro k
    rw [_root_.mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hm k

end Lev

section Level

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (hB : P.TauBimult)

include hB in

theorem eta_equiv (lv lv' : TateUniformizationInput.QLevel D l oa F)
    (h : ∀ v ∈ halfLat D l, QkPt.Equiv P F (lv.eta v) (lv'.eta v)) (v : D.La) :
    QkPt.Equiv P F (lv.eta v) (lv'.eta v) := by
  letI := H.starRing
  obtain ⟨m, hm, hm'⟩ := exists_split l
  have k : ∀ lv : TateUniformizationInput.QLevel D l oa F, QkPt.Equiv P F (lv.eta (m • v)) (lv.eta v) := fun lv => by
    have a := (add_iff_cls hB oa _ _ _).1 (lv.eta_add ((1 - m) • v) (m • v))
    rw [(zero_iff_cls hB oa _).1 ((lv.eta_ker _).2 (Submodule.smul_mem_smul hm' Submodule.mem_top)), zero_add,
      ← add_smul, sub_add_cancel, one_smul] at a
    exact (equiv_iff_cls hB oa _ _).2 a
  exact equiv_trans hB (equiv_symm hB (k lv))
    (equiv_trans hB (h _ (Submodule.smul_mem_smul hm Submodule.mem_top)) (k lv'))

variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem exists_level (I : TateIsoQ D P oa F') (eta : D.La → QkPt P F l.M) (etaA : D.La → QkPt P F l.A)
    (hA : ∀ a, QkPt.Equiv P F' (qkExt hB f hf (etaA a)) (I.ev l.A a))
    (hM : ∀ a ∈ halfLat D l, QkPt.Equiv P F' (qkExt hB f hf (eta a)) (I.ev l.M a)) :
    ∃ lv : TateUniformizationInput.QLevel D l oa F, lv.etaA = etaA ∧ ∀ a ∈ halfLat D l, lv.eta a = eta a := by
  classical
  letI := H.starRing
  have M0 : 0 < l.M := (TateUniformizationInput.levelM l).pos
  obtain ⟨m, hm, hm'⟩ := exists_split l
  have eA : ∀ a, cls hB oa (qkExt hB f hf (etaA a)) = evLin hB I l.A_pos a := fun a =>
    (equiv_iff_cls hB oa _ _).1 (hA a)
  have kill : ∀ x ∈ l.Mb, ∀ a ∈ halfLat D l, evLin hB I M0 (x • a) = 0 := fun x hx a ha => by
    rw [evLin_eq_zero, ← mem_mul_iff, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hx ha
  let eta' : D.La → QkPt P F l.M := fun a => if a ∈ halfLat D l then eta a else eta (m • a)
  have eM : ∀ a, cls hB oa (qkExt hB f hf (eta' a)) = m • evLin hB I M0 a := fun a => by
    by_cases ha : a ∈ halfLat D l
    · have k := kill _ hm' a ha
      rw [map_smul, sub_smul, one_smul, sub_eq_zero] at k
      simp only [eta', if_pos ha]
      exact ((equiv_iff_cls hB oa _ _).1 (hM a ha)).trans k
    · simp only [eta', if_neg ha]
      rw [← map_smul]
      exact (equiv_iff_cls hB oa _ _).1 (hM _ (Submodule.smul_mem_smul hm Submodule.mem_top))
  refine ⟨{ eta := eta', etaA := etaA
            eta_add := fun a a' => (add_iff_ext hB oa f hf _ _ _).2 (by rw [eM, eM, eM, map_add, smul_add])
            eta_lin := fun x a => (act_iff_ext hB oa f hf _ _ _).2 (by rw [eM, eM, map_smul, smul_comm])
            eta_ker := fun a => ?_
            eta_onto := fun p hp => ?_
            etaA_add := fun a a' => (add_iff_ext hB oa f hf _ _ _).2 (by rw [eA, eA, eA, map_add])
            etaA_lin := fun x a => (act_iff_ext hB oa f hf _ _ _).2 (by rw [eA, eA, map_smul])
            etaA_ker := fun a => by rw [zero_iff_ext hB oa f hf, eA, evLin_eq_zero]
            etaA_onto := fun p => (evLin_onto hB I l.A_pos (qkExt hB f hf p)).imp fun a k =>
              (equiv_iff_ext hB oa f hf _ _).2 ((eA a).trans k) }, rfl, fun a ha => if_pos ha⟩
  · rw [zero_iff_ext hB oa f hf, eM, ← map_smul, evLin_eq_zero, ← mem_mul_iff]
    exact smul_mem_iff hm hm' a
  · obtain ⟨a, k⟩ := evLin_onto hB I M0 (qkExt hB f hf p)
    obtain ⟨q, h₁, h₂⟩ := hp _ hm'
    have e := ((act_iff_ext hB oa f hf _ _ _).1 h₁).trans ((zero_iff_ext hB oa f hf _).1 h₂)
    rw [sub_smul, one_smul, sub_eq_zero] at e
    exact ⟨a, (equiv_iff_ext hB oa f hf _ _).2 (by rw [eM, k, ← e])⟩

omit [Module (𝓞 E) P.X] in

theorem qkExt_qkExt {F'' : Type} [Field F''] [Algebra (FractionRing R) F''] (g : F' →+* F'')
    (hg : g.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'') {k : ℕ} {p : QkPt P F k}
    {q : QkPt P F'' k} (h : QkExt (g.comp f) p q) : q = qkExt hB g hg (qkExt hB f hf p) := by
  refine DegActCompare.qkExt_unique h ?_
  have h₁ := (TorusExt.qkExt_iff hB f hf p _).2 rfl
  have h₂ := (TorusExt.qkExt_iff hB g hg (qkExt hB f hf p) _).2 rfl
  have e : spMap (g.comp f) = spMap g ≫ spMap f := by rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  refine ⟨rfl, by rw [h₂.2.1, h₁.2.1, e, Category.assoc], fun χ => corr_of_val P.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h₂.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h₁.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

end Level

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

open Classical in

theorem geom_of_input (x : TateUniformizationInput.ArcInput D c β O' b) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing O') F] (r z : O) (hr : ((β r : c.F) : ℂ) = H.rt0) (hz : ((β z : c.F) : ℂ) = zeta l.A)
    (f : O' →+* F) (hf : f = (algebraMap (FractionRing O') F).comp (algebraMap O' _)) : letI := H.starRing
    (∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct x.ac.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) x.P.X = if τ H.rt = f (b r) then D.p else D.q) ∧
    ∃ I : TateIsoQ D x.P x.ac F, (I.ζ l.A : F) = f (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (x.lev.etaA a) q → QkPt.Equiv x.P F q (I.ev l.A a)) ∧
      ∀ a ∈ halfLat D l, ∀ q, QkExt (algebraMap _ F) (x.lev.eta a) q → QkPt.Equiv x.P F q (I.ev l.M a) := by
  letI := H.starRing
  subst hf
  have hB := x.tau_bimult
  have := x.charZero
  let i : AlgebraicClosure (FractionRing O') →+* F :=
    (IsAlgClosed.lift : AlgebraicClosure (FractionRing O') →ₐ[FractionRing O'] F)
  have hi₀ : ∀ y, i (algebraMap (FractionRing O') _ y) = algebraMap (FractionRing O') F y := fun y =>
    (IsAlgClosed.lift : AlgebraicClosure (FractionRing O') →ₐ[FractionRing O'] F).commutes y
  have hi : i.comp (algebraMap (FractionRing O') _) = algebraMap (FractionRing O') F := RingHom.ext hi₀
  constructor
  · intro σ
    obtain ⟨τ, rfl⟩ := DetExtend.exists_factor i σ
    obtain ⟨n, h₁, h₂⟩ := (det_iff _).2 x.det τ
    have := x.P.P.isAb.smooth
    rw [x.gam_rt r hr] at h₂
    refine ⟨n, ?_, h₂.trans (if_congr ?_ rfl rfl)⟩
    · have e : spMap ((algebraMap (FractionRing O') F).comp (algebraMap O' _)) = spMap i ≫
          spMap ((algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp (algebraMap O' _)) := by
        rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hi]
      rw [e]
      exact (DetExtend.lieMult_extend i _ _ τ n).2 h₁
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← hi₀, i.injective.eq_iff]
  · obtain ⟨J, hζ, hA, hM⟩ := x.induced
    have key : ∀ (n : ℕ+) (p : QkPt x.P (FractionRing O') n) (a : D.La),
        TorusGraphMaps.QkMap (Algebra.ofId (FractionRing O') _) p (J.ev n a) → ∀ q, QkExt (algebraMap _ F) p q →
        QkPt.Equiv x.P F q (qkExt hB i hi ((ofQTateIso hB J).ev n a)) := fun n p a h q hq => by
      have h₀ : (algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp
        (algebraMap (FractionRing O') (FractionRing O')) = algebraMap _ _ := RingHom.ext fun _ => rfl
      rw [← hi] at hq
      rw [qkExt_qkExt hB _ h₀ i hi hq, (sameIso_of hB J n).2]
      exact qkExt_congr hB i hi ((DegActCompare.forall_qkExt_iff hB _ _ _).2 h _
        ((TorusExt.qkExt_iff hB _ h₀ _ _).2 rfl))
    refine ⟨ArcExt.tateExt i hi hB abelianSchemeLaws_all.1 (ofQTateIso hB J) (weil_ext hB i hi), ?_,
      fun a => key (TateUniformizationInput.levelA l) _ a (hA a), fun a ha => key (TateUniformizationInput.levelM l) _ a (hM a ha)⟩
    show i ((ofQTateIso hB J).ζ (TateUniformizationInput.levelA l)) = _
    rw [(sameIso_of hB J _).1, hζ, x.gam_zeta z hz, hi₀, RingHom.comp_apply]

def toArcIn (x : TateUniformizationInput.ArcInput D c β O' b) : ArcIn D l β O' b where
  D₀ := x.P
  oa := x.ac
  nontriv := x.nontriv
  even := x.psi_even
  bimult := x.tau_bimult
  gen y := (DegActCompare.psiUnitOn_iff _ y isOpen_univ).2 (x.psi_gen y)
  w0 := (DegActCompare.psiW0_host_iff H x.ac).2 x.through
  be := x.be
  be_symm := x.be_symm
  be_pos := x.be_pos
  be_adj := x.be_adj
  be_dvd := x.be_dvd
  eta := x.lev.eta
  etaA := x.lev.etaA
  geom F _ _ _ r z hr hz f hf := geom_of_input x F r z hr hz f hf

theorem exists_level_of_arcIn (a : ArcIn D l β O' b) (gam : c.F →+* FractionRing O')
    (hg : ∀ x, gam (β x) = algebraMap O' (FractionRing O') (b x)) (r z : O) (hr : ((β r : c.F) : ℂ) = H.rt0)
    (hz : ((β z : c.F) : ℂ) = zeta l.A) :
    TateUniformizationInput.GtDetCond D a.oa (AlgebraicClosure (FractionRing O'))
      (algebraMap (FractionRing O') _ (gam (TateUniformizationInput.coeffRt c))) ∧
    ∃ lv : TateUniformizationInput.QLevel D l a.oa (FractionRing O'), lv.etaA = a.etaA ∧ (∀ v ∈ halfLat D l, lv.eta v = a.eta v) ∧
      ∃ J : TateUniformizationInput.QTateIso D a.oa (AlgebraicClosure (FractionRing O')),
        J.Induces lv (Algebra.ofId (FractionRing O') _) (algebraMap (FractionRing O') _ (gam (TateUniformizationInput.coeffZeta c))) := by
  have : CharZero (FractionRing O') := (gam.charZero_iff gam.injective).1 inferInstance
  have hB := a.bimult
  obtain ⟨h₁, I, hζ, hA, hM⟩ := a.geom (AlgebraicClosure (FractionRing O')) r z hr hz _ rfl
  have er : TateUniformizationInput.coeffRt c = β r := Subtype.ext hr.symm
  have ez : TateUniformizationInput.coeffZeta c = β z := Subtype.ext hz.symm
  have h₀ : (algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp
    (algebraMap (FractionRing O') (FractionRing O')) = algebraMap _ _ := RingHom.ext fun _ => rfl
  rw [er, ez, hg, hg]
  refine ⟨(det_iff _).1 h₁, ?_⟩
  obtain ⟨lv, e₁, e₂⟩ := exists_level hB _ h₀ I a.eta a.etaA
    (fun v => hA v _ ((TorusExt.qkExt_iff hB _ h₀ _ _).2 rfl))
    (fun v hv => hM v hv _ ((TorusExt.qkExt_iff hB _ h₀ _ _).2 rfl))
  refine ⟨lv, e₁, e₂, toQTateIso hB I, hζ, fun v => ?_, fun v hv => ?_⟩
  · rw [e₁]; exact (DegActCompare.forall_qkExt_iff hB _ _ _).1 (hA v)
  · rw [e₂ v hv]; exact (DegActCompare.forall_qkExt_iff hB _ _ _).1 (hM v hv)

end ThetaShiftProofs

section Main

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

structure Core (D : Datum H) (l : Level H) (O' : Type) [CommRing O'] [IsDomain O'] where
  P : DegPre O'
  [mod : Module (𝓞 E) P.X]
  ac : letI := H.starRing; P.OAct (𝓞 E)
  be : LinearMap.BilinForm ℤ P.X
  eta : halfLat D l → QkPt P (FractionRing O') l.M
  etaA : D.La → QkPt P (FractionRing O') l.A

def coreOfArcIn (a : ArcIn D l β O' b) : Core D l O' :=
  { P := a.D₀, ac := a.oa, be := a.be, eta := fun v => a.eta v, etaA := a.etaA }

def coreOfInput (x : TateUniformizationInput.ArcInput D c β O' b) : Core D l O' :=
  { P := x.P, ac := x.ac, be := x.be, eta := fun v => x.lev.eta v, etaA := x.lev.etaA }

theorem core_toArcIn (x : TateUniformizationInput.ArcInput D c β O' b) : coreOfArcIn (toArcIn x) = coreOfInput x := rfl

def GoodBase (β : O →+* c.F) (b : O →+* O') : Prop :=
  TateUniformizationInput.IsFracImage β ∧ (∃ r, ((β r : c.F) : ℂ) = H.rt0) ∧ (∃ z, ((β z : c.F) : ℂ) = zeta l.A) ∧
    ∃ gam : c.F →+* FractionRing O', ∀ x, gam (β x) = algebraMap O' (FractionRing O') (b x)

theorem exists_input (h : GoodBase β b) (a : ArcIn D l β O' b) :
    ∃ x : TateUniformizationInput.ArcInput D c β O' b, coreOfInput x = coreOfArcIn a := by
  obtain ⟨hf, ⟨r, hr⟩, ⟨z, hz⟩, gam, hg⟩ := h
  obtain ⟨hd, lv, e₁, e₂, hI⟩ := exists_level_of_arcIn a gam hg r z hr hz
  refine ⟨{ frac := hf, gam := gam, gam_over := hg, P := a.D₀, psi_even := a.even, tau_bimult := a.bimult
            ac := a.oa, nontriv := a.nontriv
            psi_gen := fun y => (DegActCompare.psiUnitOn_iff _ y isOpen_univ).1 (a.gen y)
            through := (DegActCompare.psiW0_host_iff H a.oa).1 a.w0
            be := a.be, be_symm := a.be_symm, be_pos := a.be_pos, be_adj := a.be_adj, be_dvd := a.be_dvd
            lev := lv, det := hd, induced := hI }, ?_⟩
  have e : (fun v : halfLat D l => lv.eta v) = fun v : halfLat D l => a.eta v := funext fun v => e₂ v v.2
  simp only [coreOfInput, coreOfArcIn, e₁, e]

theorem exists_gam (hβ : Function.Injective β) (hf : TateUniformizationInput.IsFracImage β) [CharZero O'] (b : O →+* O') :
    ∃ gam : c.F →+* FractionRing O', ∀ x, gam (β x) = algebraMap O' (FractionRing O') (b x) := by
  let _ := β.toAlgebra
  have := hβ.isDomain β
  have := c.fin
  have : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective _ _).2 hβ
  have : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, s, hs, e⟩ := hf x
    exact ⟨a, s, eq_div_of_mul_eq hs e⟩
  have hb : Function.Injective b := injective_of_isAlgebraic (fun x => by
    have h : IsAlgebraic ℤ (β x) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    exact (isAlgebraic_algHom_iff β.toIntAlgHom hβ).1 h) b
  exact ⟨IsFractionRing.lift (g := (algebraMap O' (FractionRing O')).comp b)
    ((IsFractionRing.injective O' _).comp hb), fun x => IsFractionRing.lift_algebraMap _ x⟩

theorem goodBase_V (W : ValuationSubring ℂ) [CharZero O'] (b : c.V W →+* O') : GoodBase (c.V W).subtype b := by
  obtain ⟨r, z, hr, hz⟩ := ArcInTest.exists_values c W
  exact ⟨TateUniformizationInput.isFracImage_V W, ⟨r, hr⟩, ⟨z, hz⟩, exists_gam Subtype.val_injective (TateUniformizationInput.isFracImage_V W) b⟩

theorem goodBase_id (b : c.F →+* O') : GoodBase (RingHom.id c.F) b :=
  ⟨fun x => ⟨x, 1, one_ne_zero, _root_.mul_one x⟩, ⟨TateUniformizationInput.coeffRt c, rfl⟩, ⟨TateUniformizationInput.coeffZeta c, rfl⟩,
    (algebraMap O' _).comp b, fun _ => rfl⟩

theorem differ_over_int (D : Datum H) (c : Coeff l) :
    Nonempty (ArcIn D l (Int.castRingHom c.F) c.F (Int.castRingHom c.F)) ∧
      IsEmpty (TateUniformizationInput.ArcInput D c (Int.castRingHom c.F) c.F (Int.castRingHom c.F)) := by
  refine ⟨ArcInTest.nonempty_int D c, ⟨fun x => ?_⟩⟩
  obtain ⟨a, s, hs, e⟩ := x.frac (TateUniformizationInput.coeffRt c)
  have e' : H.rt0 * (s : ℂ) = (a : ℂ) := by simpa [TateUniformizationInput.coeffRt_val] using congrArg (fun y : c.F => (y : ℂ)) e
  have h₁ : ((a ^ 2 : ℤ) : ℂ) = ((-(H.d : ℤ) * s ^ 2 : ℤ) : ℂ) := by
    push_cast
    rw [← e', mul_pow, H.sqrt_neg_disc_sq]
  have h₂ : a ^ 2 = -(H.d : ℤ) * s ^ 2 := Int.cast_injective h₁
  have h₃ : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  have h₄ : (0 : ℤ) < H.d := Int.natCast_pos.2 H.d_prime.pos
  nlinarith [sq_nonneg a, mul_pos h₄ (sq_pos_of_ne_zero h₃)]

end Main

theorem typings_agree (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) :
    (∀ (R : Type) [CommRing R] [IsDomain R] (P : DegPre R) [Module (𝓞 E) P.X]
      (oa : letI := H.starRing; P.OAct (𝓞 E)) (F : Type) [Field F] [Algebra (FractionRing R) F],
      (P.TauBimult → (∀ I : TateIsoQ D P oa F, ∃ J : TateUniformizationInput.QTateIso D oa F, SameIso I J) ∧
        (∀ J : TateUniformizationInput.QTateIso D oa F, ∃ I : TateIsoQ D P oa F, SameIso I J) ∧
        ∀ (l : Level H) (lv lv' : TateUniformizationInput.QLevel D l oa F),
          (∀ v ∈ halfLat D l, QkPt.Equiv P F (lv.eta v) (lv'.eta v)) → ∀ v, QkPt.Equiv P F (lv.eta v) (lv'.eta v)) ∧
      (CharZero F → ∀ ρ : F, (letI := H.starRing
        ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oa.onB.toRingAct)
          (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
          n + Module.finrank (𝓞 E) P.X = open Classical in if τ H.rt = ρ then D.p else D.q) ↔
        TateUniformizationInput.GtDetCond D oa F ρ)) ∧
    ∀ (l : Level H) (c : Coeff l) (O' : Type) [CommRing O'] [IsDomain O'],
      (∀ (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* O'),
        (∀ x : TateUniformizationInput.ArcInput D c β O' b, ∃ a : ArcIn D l β O' b,
          coreOfArcIn a = coreOfInput x ∧ HEq a.eta x.lev.eta) ∧
        (GoodBase β b → Set.range (coreOfArcIn (D := D) (β := β) (b := b)) =
          Set.range (coreOfInput (D := D) (β := β) (b := b)))) ∧
      (CharZero O' → ∀ (W : ValuationSubring ℂ) (b : c.V W →+* O'), GoodBase (c.V W).subtype b) ∧
      ∀ b : c.F →+* O', GoodBase (RingHom.id c.F) b :=
  ⟨fun _ _ _ _ _ _ _ _ _ => ⟨fun hB => ⟨fun I => ⟨_, sameIso_to hB I⟩, fun J => ⟨_, sameIso_of hB J⟩,
      fun _ => eta_equiv hB⟩, fun _ => det_iff⟩,
    fun _ _ _ _ _ => ⟨fun _ _ _ _ => ⟨fun x => ⟨toArcIn x, rfl, HEq.rfl⟩, fun h => Set.ext fun _ =>
      ⟨fun ⟨a, e⟩ => (exists_input h a).imp fun _ e' => e'.trans e, fun ⟨x, e⟩ => ⟨toArcIn x, e⟩⟩⟩,
      fun _ W b => goodBase_V W b, goodBase_id⟩⟩

end GlobalTheory.ArcInputCompare
