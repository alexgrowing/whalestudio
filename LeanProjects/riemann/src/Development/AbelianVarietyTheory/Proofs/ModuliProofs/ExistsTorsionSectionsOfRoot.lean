import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TorsionSections

open GlobalTheory.LevCover

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {pr : ℕ → Q → Q → kˣ → Prop}

def PtCond (I : TateIso D k Q act pr) (M : ℕ) (w : kˣ) (e f : 𝓞 E) {J : Type} (rep : J → D.La) (a b : D.La)
    (y : Q) : Prop :=
  y ^ M = 1 ∧ act e y = I.ev M (e • a) ∧ ∀ j, pr M y (I.ev M (f • rep j)) (w ^ D.EF b (f • rep j))

theorem zpow_congr {M : ℕ} {w : kˣ} (hw : IsPrimitiveRoot w M) {m n : ℤ} :
    w ^ m = w ^ n ↔ (M : ℤ) ∣ m - n := by
  rw [← hw.zpow_eq_one_iff_dvd, zpow_sub, mul_inv_eq_one]

variable (I : TateIso D k Q act pr) {M : ℕ} (hM : 0 < M) {w : kˣ} (hw : IsPrimitiveRoot w M) {e f t : 𝓞 E}
  (ht : e * (1 - e) = M * t) (hf : ∀ x c, D.EF x (f • c) = D.EF ((1 - e) • x) c) {J : Type} {rep : J → D.La}
  (hrep : ∀ a, ∃ j d, a = rep j + M • d)

include hM hw ht hf in
theorem exists_ptCond (a b : D.La) : ∃ y, PtCond I M w e f rep a b y := by
  obtain ⟨v, -, hv⟩ := exists_coprime_zpow hM (I.ζ_prim M hM) hw
  have hs : ∀ x : D.La, (e * (1 - e)) • x = M • (t • x) := fun x => by
    rw [ht, mul_smul, Nat.cast_smul_eq_nsmul]
  refine ⟨I.ev M (e • a + (1 - e) • v • b), (I.onto M hM _).2 ⟨_, rfl⟩, ?_, fun j => ?_⟩
  · rw [← I.lin, tateIso_ev_eq_iff I hM]
    refine ⟨t • (v • b - a), ?_⟩
    rw [← hs]
    module
  · have h := I.isom M hM (e • a + (1 - e) • v • b) (f • rep j)
    rw [hv, ← zpow_mul]
    refine (zpow_congr (I.ζ_prim M hM)).2 ?_ ▸ h
    have e1 : (1 - e) • (e • a + (1 - e) • v • b) = v • (1 - e) • b + M • (t • (a - v • b)) := by
      rw [← hs]
      module
    rw [hf, hf, e1]
    refine ⟨D.EF (t • (a - v • b)) (rep j), ?_⟩
    simp only [map_add, map_nsmul, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, smul_eq_mul]
    ring

include hM hw hf hrep in
theorem ptCond_unique (hu : ∀ x y c c', pr M x y c → pr M x y c' → c = c') {a b : D.La} {y y' : Q}
    (h : PtCond I M w e f rep a b y) (h' : PtCond I M w e f rep a b y') : y = y' := by
  obtain ⟨x, rfl⟩ := (I.onto M hM y).1 h.1
  obtain ⟨x', rfl⟩ := (I.onto M hM y').1 h'.1
  obtain ⟨c, hc⟩ := (tateIso_ev_eq_iff I hM _ _).1
    ((I.lin M e x).trans (h.2.1.trans (h'.2.1.symm.trans (I.lin M e x').symm)))
  have h1 : ∀ z, (M : ℤ) ∣ D.EF ((1 - e) • (x - x')) z := fun z => by
    obtain ⟨j, d, rfl⟩ := hrep z
    have h2 := (zpow_congr (I.ζ_prim M hM)).1 ((hu _ _ _ _ (I.isom M hM x _) (h.2.2 j)).trans
      (hu _ _ _ _ (h'.2.2 j) (I.isom M hM x' _)))
    rw [hf, hf, ← LinearMap.sub_apply, ← map_sub, ← smul_sub] at h2
    rw [map_add, map_nsmul, nsmul_eq_mul]
    exact dvd_add h2 (dvd_mul_right _ _)
  choose g hg using h1
  have hM' : (M : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  let φ : D.La →ₗ[ℤ] ℤ := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' g fun z z' =>
    mul_left_cancel₀ hM' (by rw [mul_add, ← hg, ← hg, ← hg, map_add]))
  obtain ⟨c', hc'⟩ := D.unimod.2 φ
  have h3 : (1 - e) • (x - x') = M • c' := D.unimod.1 (LinearMap.ext fun z => by
    rw [hg, map_nsmul, hc', LinearMap.smul_apply, nsmul_eq_mul]
    rfl)
  rw [tateIso_ev_eq_iff I hM]
  refine ⟨c + c', ?_⟩
  rw [smul_add, ← hc, ← h3]
  module

include hM hw hrep in
theorem exists_index {y : Q} (hy : y ^ M = 1) : ∃ i j, PtCond I M w e f rep (rep i) (rep j) y := by
  obtain ⟨x, rfl⟩ := (I.onto M hM y).1 hy
  obtain ⟨v, -, hv⟩ := exists_coprime_zpow hM hw (I.ζ_prim M hM)
  obtain ⟨i, d, hi⟩ := hrep x
  obtain ⟨j, d', hj⟩ := hrep (v • x)
  refine ⟨i, j, hy, ?_, fun c => ?_⟩
  · rw [← I.lin, tateIso_ev_eq_iff I hM]
    refine ⟨e • d, ?_⟩
    rw [hi]
    module
  · have h := I.isom M hM x (f • rep c)
    rw [hv, ← zpow_mul] at h
    refine (zpow_congr hw).2 ?_ ▸ h
    refine ⟨D.EF d' (f • rep c), ?_⟩
    have := congrArg (fun z => D.EF z (f • rep c)) hj
    simp only [map_add, map_nsmul, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
      smul_eq_mul] at this
    linarith

end Lattice

section Clopen

variable {S : Scheme.{0}}

theorem exists_section {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] {P : ∀ T : Over S, (T ⟶ Z) → Prop}
    (hP : ClopenCond Z P)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃! z : Over.mk x ⟶ Z, P _ z) :
    ∃ σ : 𝟙_ (Over S) ⟶ Z, ∀ (T : Over S) (z : T ⟶ Z), P T z ↔ z = toUnit T ≫ σ := by
  obtain ⟨U, hU, HU⟩ := hP
  obtain ⟨V, i, h1, h2, h3, Hi⟩ := exists_sub U hU
  have : IsFinite (𝟙_ (Over S)).hom := inferInstanceAs (IsFinite (𝟙 S))
  have : Etale (𝟙_ (Over S)).hom := inferInstanceAs (Etale (𝟙 S))
  have : IsIso (toUnit V) := by
    refine (FinEt.isIso_iff_bijective_over_algClosed _).2 fun k _ _ x => ?_
    obtain ⟨z, hz, hu⟩ := h k x
    obtain ⟨v, -⟩ := (Hi _ z).1 ((HU _ z).1 hz)
    refine ⟨fun v₁ v₂ _ => (cancel_mono i).1 ?_, fun y => ⟨v, toUnit_unique _ _⟩⟩
    exact (hu _ ((HU _ _).2 ((Hi _ _).2 ⟨v₁, rfl⟩))).trans (hu _ ((HU _ _).2 ((Hi _ _).2 ⟨v₂, rfl⟩))).symm
  refine ⟨inv (toUnit V) ≫ i, fun T z => ?_⟩
  rw [HU, Hi]
  refine ⟨?_, fun e => ⟨toUnit T ≫ inv (toUnit V), by rw [e, Category.assoc]⟩⟩
  rintro ⟨v, rfl⟩
  rw [toUnit_unique (toUnit T) (v ≫ toUnit V), Category.assoc, IsIso.hom_inv_id_assoc]

theorem torsion_ext (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} {u u' : T ⟶ torsion G n}
    (h : u ≫ torsion.ι G n = u' ≫ torsion.ι G n) : u = u' :=
  (LatticeTorsion.existsUnique_torsion G n (u' ≫ torsion.ι G n)
    (by rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])).unique h rfl

theorem clopenCond_torsion_eq {G : Over S} [GrpObj G] {n : ℕ} [IsFinite (torsion G n).hom] [Etale (torsion G n).hom]
    {T : Over S} {x y : T ⟶ G} (hx : x ^ n = 1) (hy : y ^ n = 1) : ClopenCond T fun _ h => h ≫ x = h ≫ y := by
  obtain ⟨u, rfl, -⟩ := LatticeTorsion.existsUnique_torsion G n x hx
  obtain ⟨u', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G n y hy
  refine (clopenCond_eq u u').congr fun T' h => ⟨fun H => torsion_ext G n ?_, fun H => ?_⟩
  · rw [Category.assoc, Category.assoc, H]
  · rw [← Category.assoc, H, Category.assoc]

theorem map_fnOn_comp {L : Type} [CommRing L] {T T' : Scheme.{0}} (g : T ⟶ Sp L) (h : T' ⟶ T) (c : Lˣ) :
    Units.map h.appTop.hom.toMonoidHom (Units.map (fnOn g).toMonoidHom c) =
      Units.map (fnOn (h ≫ g)).toMonoidHom c := by
  apply Units.ext
  exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c))
    (Scheme.Hom.comp_appTop h g)).symm

theorem map_fnOn_spMap {L k : Type} [CommRing L] [CommRing k] (β : L →+* k) (c : Lˣ) :
    Units.map (fnOn (spMap β)).toMonoidHom c = unitOn (Units.map β.toMonoidHom c) := by
  rw [← map_fnOn (𝟙 _) (spMap β) β (Category.comp_id _), map_fnOn_comp, Category.comp_id]

end Clopen

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B F : Type} [CommRing B] [Field F] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def SecCond (o : Obj D l b s) (sF : S ⟶ Sp F) (z : Fˣ) (e f : 𝓞 E) {J : Type} (rep : J → D.La) (a a' : D.La)
    (T : Over S) (y : T ⟶ o.t.G) : Prop :=
  y ^ l.M = 1 ∧ y ≫ o.t.act.act e = toUnit T ≫ o.eta (e • a) ∧
    ∀ j, Out.WeilIs o.t.G o.t.PP.L l.M y (toUnit T ≫ o.eta (f • rep j))
      (Units.map (fnOn (T.hom ≫ sF)).toMonoidHom (z ^ D.EF a' (f • rep j)))

theorem eta_pow (o : Obj D l b s) (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [← add_map_nsmul o.eta_add, o.eta_ker _ (nsmul_M_mem l a)]

theorem exists_secCond_iff (o : Obj D l b s) (sF : S ⟶ Sp F) {z : Fˣ} (hz : IsPrimitiveRoot z l.M)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) :
    ∃ (I : TateAt D o.t x) (w : kˣ), IsPrimitiveRoot w l.M ∧ ∀ e ∈ Mc l, ∀ f ∈ Mc l, ∀ (J : Type) (rep : J → D.La)
      (a a' : D.La) (y : Over.mk x ⟶ o.t.G), SecCond o sF z e f rep a a' _ y ↔ PtCond I l.M w e f rep a a' y := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨δ, hδ⟩ := exists_spMap (x ≫ sF)
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x β hβ
  refine ⟨I, Units.map δ.toMonoidHom z, hz.map_of_injective (Units.map_injective δ.injective),
    fun e he f hf J rep a a' y => ?_⟩
  refine and_congr Iff.rfl (and_congr ?_ (forall_congr' fun j => ?_))
  · rw [hI _ (Submodule.smul_mem_smul he Submodule.mem_top)]
  · rw [hI _ (Submodule.smul_mem_smul hf Submodule.mem_top)]
    refine iff_of_eq (congrArg (Out.WeilIs o.t.G o.t.PP.L l.M y _) ?_)
    show Units.map (fnOn (x ≫ sF)).toMonoidHom _ = _
    rw [hδ, map_fnOn_spMap, map_zpow]

theorem exists_section_secCond (hL : Out.Laws) [IsLocallyNoetherian S] (o : Obj D l b s) (sF : S ⟶ Sp F) {z : Fˣ}
    (hz : IsPrimitiveRoot z l.M) {e : 𝓞 E} (he : e ∈ Mc l) (he' : 1 - e ∈ l.Mb) {J : Type} [Finite J]
    {rep : J → D.La} (hrep : ∀ a, ∃ j d, a = rep j + l.M • d) (a a' : D.La) :
    ∃ σ : 𝟙_ (Over S) ⟶ o.t.G, ∀ (T : Over S) (y : T ⟶ o.t.G),
      SecCond o sF z e (H.bar (1 - e)) rep a a' T y ↔ y = toUnit T ≫ σ := by
  have hu : ∀ {T : Scheme.{0}} (g : T ⟶ S), IsUnit (l.M : Γ(T, ⊤)) := fun g => by
    have := (b.unit l.M (M_pos l)).map (fnOn (g ≫ s))
    rwa [map_natCast] at this
  have hab := ObjDim.isAbelianScheme o
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion o.t.G (hu (𝟙 S))
  have hι := LatticeTorsion.torsionι_pow_eq_one o.t.G l.M
  have hη : ∀ (T : Over S) c, (toUnit T ≫ o.eta c) ^ l.M = 1 := fun T c => by
    rw [← MonObj.comp_pow, eta_pow, MonObj.comp_one]
  have hact := o.t.act.hom e
  have c1 := clopenCond_torsion_eq (n := l.M) (x := torsion.ι o.t.G l.M ≫ o.t.act.act e)
    (by rw [← MonObj.pow_comp, hι, MonObj.one_comp]) (hη _ (e • a))
  have c2 := ClopenCond.forall_finite (T := torsion o.t.G l.M) (J := J) fun j =>
    PairingLocus.exists_clopen_of_isLocallyNoetherian hL S (Obj.toPolAV o) l.M (torsion o.t.G l.M)
      (torsion.ι o.t.G l.M) (toUnit _ ≫ o.eta (H.bar (1 - e) • rep j))
      (Units.map (fnOn ((torsion o.t.G l.M).hom ≫ sF)).toMonoidHom (z ^ D.EF a' (H.bar (1 - e) • rep j)))
      (hu (torsion o.t.G l.M).hom) hι (hη _ _) (by
        rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz.pow_eq_one, one_zpow, map_one])
  have c3 : ClopenCond (torsion o.t.G l.M) fun T h =>
      SecCond o sF z e (H.bar (1 - e)) rep a a' T (h ≫ torsion.ι o.t.G l.M) := by
    refine (c1.and c2).congr fun T h => ?_
    have h1 : ∀ c, h ≫ toUnit _ ≫ o.eta c = toUnit T ≫ o.eta c := fun c => by
      rw [← Category.assoc, toUnit_unique (h ≫ toUnit _) (toUnit T)]
    refine (and_iff_right (by rw [← MonObj.comp_pow, hι, MonObj.comp_one])).trans
      (and_congr (by rw [h1, Category.assoc]) (forall_congr' fun j => ?_))
    rw [map_fnOn_comp, ← Category.assoc h.left, Over.w h]
    exact iff_of_eq (congrArg (fun y => Out.WeilIs o.t.G o.t.PP.L l.M _ y _) (h1 _).symm)
  obtain ⟨t, ht⟩ : ∃ t, e * (1 - e) = l.M * t := by
    have : (1 - e) * e ∈ Ideal.span {(l.M : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul he' he
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 this
    exact ⟨t, by rw [mul_comm e, ht]⟩
  have hf : ∀ x c, D.EF x (H.bar (1 - e) • c) = D.EF ((1 - e) • x) c := fun x c => (D.adj _ _ _).symm
  obtain ⟨σ, hσ⟩ := exists_section c3 fun k _ _ x => by
    obtain ⟨I, w, hw, HI⟩ := exists_secCond_iff o sF hz x
    replace HI := HI e he _ (Ideal.mem_map_of_mem _ he') J rep a a'
    obtain ⟨y, hy⟩ := exists_ptCond I (M_pos l) hw ht hf (rep := rep) a a'
    obtain ⟨u, rfl, -⟩ := LatticeTorsion.existsUnique_torsion o.t.G l.M y hy.1
    exact ⟨u, (HI _).2 hy, fun u' hu' => torsion_ext _ _ (ptCond_unique I (M_pos l) hw hf hrep
      (fun y y' c c' => weilIs_unique_fieldPoint S o.t.G o.t.PP.L o.t.PP.isLB k x l.M y y' c c') ((HI _).1 hu') hy)⟩
  refine ⟨σ ≫ torsion.ι o.t.G l.M, fun T y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨u, rfl, -⟩ := LatticeTorsion.existsUnique_torsion o.t.G l.M y hy.1
    rw [(hσ T u).1 hy, Category.assoc]
  · rintro rfl
    rw [← Category.assoc]
    exact (hσ T _).2 rfl

theorem SecCond.push {o : Obj D l b s} {sF : S ⟶ Sp F} {z : Fˣ} {e f : 𝓞 E} {J : Type} {rep : J → D.La}
    {a a' : D.La} {T : Over S} {y : T ⟶ o.t.G} (h : SecCond o sF z e f rep a a' T y) {r : S ⟶ S}
    (ν : SABMap o.t o.t r) (hr : r ≫ sF = sF) (hν : ∀ x, (o.eta x).left ≫ ν.φ = r ≫ (o.eta x).left) :
    SecCond o sF z e f rep a a' _ (ObjPull.pushEquiv ν.cart T y) := by
  have h1 : ∀ c, (toUnit (Over.mk (T.hom ≫ r)) ≫ o.eta c).left = (toUnit T ≫ o.eta c).left ≫ ν.φ := fun c => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hν, ObjPull.toUnit_left', ObjPull.toUnit_left']
    exact Category.assoc _ _ _
  refine ⟨by rw [← map_pow, h.1, map_one], ?_, fun j => ?_⟩
  · rw [← pushEquiv_act, h.2.1]
    exact Over.OverMorphism.ext (h1 _).symm
  · have h2 := (weilIs_grpPullback_of_comm _ _ o.t.G o.t.G r ν.cm.F o.t.PP.L o.t.PP.L o.t.PP.isLB o.t.PP.isLB ν.cart
      (sabMap_lbIso ν) T l.M _ _ (ObjPull.pushEquiv ν.cart T y) _ _ rfl (h1 _)).1 (h.2.2 j)
    have h3 : (Over.mk (T.hom ≫ r)).hom ≫ sF = T.hom ≫ sF := (Category.assoc _ _ _).trans (congrArg _ hr)
    rw [h3]
    exact h2

end Object

end GlobalTheory.TorsionSections

namespace GlobalTheory

open LevCover TorsionSections

theorem exists_torsion_sections_of_root : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F : Type) [CommRing B] [Field F] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (sF : S ⟶ Sp F) (o : Obj D l b s) (z : F), IsReduced S → IsLocallyNoetherian S → IsPrimitiveRoot z l.M → ∃ (I : Type) (_ : Finite I) (σ : I → (𝟙_ (Over S) ⟶ o.t.G)), (∀ i, σ i ^ l.M = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ S) (y : Over.mk u ⟶ o.t.G), y ^ l.M = 1 → ∃ i, y.left = u ≫ (σ i).left) ∧ ∀ (r : S ⟶ S) (ν : SABMap o.t o.t r), r ≫ sF = sF → (∀ x, (o.eta x).left ≫ ν.φ = r ≫ (o.eta x).left) → ∀ i, (σ i).left ≫ ν.φ = r ≫ (σ i).left := by
  intro hL _ _ E _ _ _ H D l B F _ _ b S s sF o z _ _ hz
  obtain ⟨u, rfl⟩ := hz.isUnit (M_pos l).ne'
  have hu : IsPrimitiveRoot u l.M := IsPrimitiveRoot.coe_units_iff.1 hz
  obtain ⟨e, he, he'⟩ := exists_idem l
  obtain ⟨_, _⟩ := datum_free D
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La (M_pos l)
  let rep : Set.range q → D.La := fun c => c.2.choose
  have hrep : ∀ a, ∃ j d, a = rep j + l.M • d := fun a =>
    ⟨⟨q a, a, rfl⟩, hq _ _ (⟨a, rfl⟩ : q a ∈ Set.range q).choose_spec⟩
  choose σ hσ using exists_section_secCond hL o sF hu he he' hrep
  have h0 : ∀ a a', SecCond o sF u e (H.bar (1 - e)) rep a a' _ (σ a a') := fun a a' =>
    (hσ a a' _ _).2 (by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
  refine ⟨Set.range q × Set.range q, inferInstance, fun i => σ (rep i.1) (rep i.2), fun i => (h0 _ _).1,
    fun k _ _ x y hy => ?_, fun r ν hr hν i => ?_⟩
  · obtain ⟨I, w, hw, HI⟩ := exists_secCond_iff o sF hu x
    obtain ⟨i, j, h⟩ := exists_index I (M_pos l) hw (e := e) (f := H.bar (1 - e)) hrep hy
    refine ⟨(i, j), ?_⟩
    rw [(hσ _ _ _ _).1 ((HI e he _ (Ideal.mem_map_of_mem _ he') _ rep _ _ y).2 h), Over.comp_left,
      ObjPull.toUnit_left']
    rfl
  · have h := congrArg Over.Hom.left ((hσ _ _ _ _).1 ((h0 (rep i.1) (rep i.2)).push ν hr hν))
    rw [Over.comp_left, ObjPull.toUnit_left'] at h
    exact h.trans (congrArg (· ≫ _) (Category.id_comp r))

end GlobalTheory
