import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}}

theorem resG_resG {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  change (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (u : Γ(X, U)) := rfl

theorem germ_resG {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (a : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom (resG X h a) = (X.presheaf.germ U x (h hx)).hom a :=
  X.presheaf.germ_res_apply (homOfLE h) x hx a

theorem ext_germ {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ x (hx : x ∈ U), (X.presheaf.germ U x hx).hom a = (X.presheaf.germ U x hx).hom b) :
    a = b :=
  TopCat.Presheaf.section_ext X.sheaf U a b h

theorem app_resG (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (φ.app V).hom (resG X h a) = resG Y (φ.preimage_mono h) ((φ.app U).hom a) := by
  change ((X.presheaf.map (homOfLE h).op ≫ φ.app V).hom) a = _
  rw [Scheme.Hom.naturality]
  rfl

def IsRegularFn {U : X.Opens} (a : Γ(X, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), resG X h a ∈ nonZeroDivisors Γ(X, V)

namespace IsRegularFn

variable {U : X.Opens} {a b : Γ(X, U)}

theorem mem (ha : IsRegularFn a) : a ∈ nonZeroDivisors Γ(X, U) := by
  have := ha U le_rfl
  rwa [resG_self] at this

theorem resG (ha : IsRegularFn a) {V : X.Opens} (h : V ≤ U) : IsRegularFn (resG X h a) :=
  fun W hW => by rw [resG_resG]; exact ha W _

theorem mul (ha : IsRegularFn a) (hb : IsRegularFn b) : IsRegularFn (a * b) :=
  fun W hW => by rw [map_mul]; exact mul_mem (ha W hW) (hb W hW)

theorem pow (ha : IsRegularFn a) (n : ℕ) : IsRegularFn (a ^ n) :=
  fun W hW => by rw [map_pow]; exact pow_mem (ha W hW) n

theorem of_isUnit (ha : IsUnit a) : IsRegularFn a :=
  fun _ hW => (ha.map (Geo.Tor.resG X hW)).mem_nonZeroDivisors

theorem of_dvd (hb : IsRegularFn b) (h : a ∣ b) : IsRegularFn a := fun W hW => by
  obtain ⟨c, rfl⟩ := h
  have := hb W hW
  rw [map_mul] at this
  exact (mul_mem_nonZeroDivisors.1 this).1

theorem mul_right_cancel (ha : IsRegularFn a) {c d : Γ(X, U)} (h : c * a = d * a) : c = d :=
  (mul_cancel_right_mem_nonZeroDivisors ha.mem).1 h

end IsRegularFn

theorem isRegularFn_iff_germ {U : X.Opens} {a : Γ(X, U)} :
    IsRegularFn a ↔ ∀ x (hx : x ∈ U),
      (X.presheaf.germ U x hx).hom a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  constructor
  · intro ha x hx
    refine mem_nonZeroDivisors_iff_right.2 fun t ht => ?_
    obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq t
    have hm : x ∈ U ⊓ V := ⟨hx, hV⟩
    have e : (X.presheaf.germ (U ⊓ V) x hm).hom (resG X inf_le_right b * resG X inf_le_left a) =
        (X.presheaf.germ (U ⊓ V) x hm).hom 0 := by
      rw [map_mul, germ_resG, germ_resG, map_zero]; exact ht
    obtain ⟨W, hW, i₁, i₂, e'⟩ := X.presheaf.germ_eq x hm hm _ _ e
    have le : W ≤ U ⊓ V := i₁.le
    have e'' : resG X le (resG X inf_le_right b * resG X inf_le_left a) = resG X le 0 := e'
    rw [map_mul, resG_resG, resG_resG, map_zero] at e''
    have hb := mem_nonZeroDivisors_iff_right.1 (ha W _) _ e''
    rw [← germ_resG (le.trans inf_le_right) x hW b, hb, map_zero]
  · intro h V hV
    refine mem_nonZeroDivisors_iff_right.2 fun t ht => ext_germ fun x hx => ?_
    have := congrArg (X.presheaf.germ V x hx).hom ht
    rw [map_mul, germ_resG, map_zero] at this
    rw [map_zero]
    exact mem_nonZeroDivisors_iff_right.1 (h x (hV hx)) _ this

theorem isRegularFn_of_locally {U : X.Opens} {a : Γ(X, U)}
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ IsRegularFn (resG X hV a)) :
    IsRegularFn a := by
  refine isRegularFn_iff_germ.2 fun x hx => ?_
  obtain ⟨V, hV, hxV, hr⟩ := h x hx
  have := isRegularFn_iff_germ.1 hr x hxV
  rwa [germ_resG] at this

theorem isRegularFn_iff_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)} :
    IsRegularFn a ↔ a ∈ nonZeroDivisors Γ(X, U) := by
  refine ⟨IsRegularFn.mem, fun ha => isRegularFn_iff_germ.2 fun x hx => ?_⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.nonZeroDivisors_le_comap (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) ha

theorem isRegularFn_of_ne_zero [IsIntegral X] {U : X.Opens} {a : Γ(X, U)} (ha : a ≠ 0) :
    IsRegularFn a :=
  isRegularFn_iff_germ.2 fun x hx => mem_nonZeroDivisors_of_ne_zero fun h =>
    ha (germ_injective_of_isIntegral X x hx (h.trans (map_zero _).symm))

theorem IsRegularFn.ne_zero {U : X.Opens} [hU : Nonempty U] {a : Γ(X, U)} (ha : IsRegularFn a) :
    a ≠ 0 := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  rintro rfl
  have := isRegularFn_iff_germ.1 ha x hx
  rw [map_zero] at this
  exact zero_notMem_nonZeroDivisors this

theorem isRegularFn_iff_ne_zero [IsIntegral X] {U : X.Opens} [Nonempty U] {a : Γ(X, U)} :
    IsRegularFn a ↔ a ≠ 0 :=
  ⟨IsRegularFn.ne_zero, isRegularFn_of_ne_zero⟩

theorem IsRegularFn.app_of_flat (φ : Y ⟶ X) [Flat φ] {U : X.Opens} {a : Γ(X, U)}
    (ha : IsRegularFn a) : IsRegularFn ((φ.app U).hom a) := by
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  let _ := (φ.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (φ y)) (Y.presheaf.stalk y) := Flat.stalkMap φ y
  have h1 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y)
    (isRegularFn_iff_germ.1 ha (φ y) hy)
  have e := Scheme.Hom.germ_stalkMap_apply φ U y hy a
  refine mem_nonZeroDivisors_iff_left.2 fun t ht => h1 ?_
  change (φ.stalkMap y).hom _ * t = (φ.stalkMap y).hom _ * 0
  rw [mul_zero]
  exact (congrArg (· * t) e).trans ht

theorem IsRegularFn.dvd_of_germ {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (h : ∀ x (hx : x ∈ U), (X.presheaf.germ U x hx).hom a ∣ (X.presheaf.germ U x hx).hom b) :
    a ∣ b := by
  have loc : ∀ x : U, ∃ (V : X.Opens) (hV : V ≤ U) (_ : x.1 ∈ V) (c : Γ(X, V)),
      Geo.Tor.resG X hV b = c * Geo.Tor.resG X hV a := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := h x hx
    obtain ⟨V, hV, c, rfl⟩ := X.presheaf.exists_germ_eq t
    have hm : x ∈ U ⊓ V := ⟨hx, hV⟩
    have e : (X.presheaf.germ (U ⊓ V) x hm).hom (Geo.Tor.resG X inf_le_left b) =
        (X.presheaf.germ (U ⊓ V) x hm).hom
          (Geo.Tor.resG X inf_le_right c * Geo.Tor.resG X inf_le_left a) := by
      rw [map_mul, germ_resG, germ_resG, germ_resG, ht, mul_comm]
    obtain ⟨W, hW, i₁, i₂, e'⟩ := X.presheaf.germ_eq x hm hm _ _ e
    have le : W ≤ U ⊓ V := i₁.le
    have e'' : Geo.Tor.resG X le (Geo.Tor.resG X inf_le_left b) = Geo.Tor.resG X le
      (Geo.Tor.resG X inf_le_right c * Geo.Tor.resG X inf_le_left a) := e'
    rw [map_mul, resG_resG, resG_resG, resG_resG] at e''
    exact ⟨W, le.trans inf_le_left, hW, _, e''⟩
  choose V hV hx c hc using loc
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hV i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) c (fun i j => by
      have e₁ := congrArg (Geo.Tor.resG X (inf_le_left : V i ⊓ V j ≤ V i)) (hc i)
      have e₂ := congrArg (Geo.Tor.resG X (inf_le_right : V i ⊓ V j ≤ V j)) (hc j)
      rw [map_mul, resG_resG, resG_resG] at e₁ e₂
      exact (ha.resG (inf_le_left.trans (hV i))).mul_right_cancel (e₁.symm.trans e₂))
  refine ⟨s, ext_germ fun x hx' => ?_⟩
  have e := congrArg (X.presheaf.germ _ x (hx ⟨x, hx'⟩)).hom (hc ⟨x, hx'⟩)
  have hs' : ∀ s' : Γ(X, U), Geo.Tor.resG X (hV ⟨x, hx'⟩) s' = c ⟨x, hx'⟩ →
      (X.presheaf.germ U x hx').hom b = (X.presheaf.germ U x hx').hom (a * s') := fun s' hs' => by
    rw [← hs', ← map_mul (Geo.Tor.resG X _), germ_resG, germ_resG, mul_comm] at e
    exact e
  exact hs' s (hs ⟨x, hx'⟩)

theorem IsRegularFn.associated_of_dvd_dvd {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (h₁ : a ∣ b) (h₂ : b ∣ a) : Associated a b := by
  obtain ⟨c, rfl⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have : c * d = 1 := ha.mul_right_cancel (by rw [one_mul]; linear_combination -hd)
  exact ⟨Units.mkOfMulEqOne c d this, rfl⟩

theorem IsRegularFn.associated_of_germ {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (hb : IsRegularFn b)
    (h : ∀ x (hx : x ∈ U), Ideal.span {(X.presheaf.germ U x hx).hom a} =
      Ideal.span {(X.presheaf.germ U x hx).hom b}) : Associated a b :=
  ha.associated_of_dvd_dvd
    (ha.dvd_of_germ fun x hx => Ideal.span_singleton_le_span_singleton.1 (h x hx).ge)
    (hb.dvd_of_germ fun x hx => Ideal.span_singleton_le_span_singleton.1 (h x hx).le)

theorem sec_ext {L : LB X} {s t : L.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  obtain ⟨s, _⟩ := s
  obtain ⟨t, _⟩ := t
  obtain rfl : s = t := funext h
  rfl

theorem sec_compat {L : LB X} (s : L.Sec) (i j : L.ι) {W : X.Opens} (hi : W ≤ L.U i)
    (hj : W ≤ L.U j) :
    resG X hi (s.f i) = resG X (le_inf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (s.f j) := by
  have := congrArg (resG X (le_inf hi hj)) (s.compat i j)
  rwa [map_mul, resG_resG, resG_resG] at this

def IsRegularSec {L : LB X} (s : L.Sec) : Prop := ∀ i, IsRegularFn (s.f i)

def SecMaps {A B : LB X} (w : LB.Iso A B) (a : A.Sec) (b : B.Sec) : Prop :=
  ∀ p : B.ι × A.ι, resG X (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ B.U p.1) (b.f p.1) =
    (@id (Γ(X, B.U p.1 ⊓ A.U p.2)ˣ) (w.s p) : Γ(X, B.U p.1 ⊓ A.U p.2)) *
      resG X (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ A.U p.2) (a.f p.2)

theorem SecMaps.on {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec} (h : SecMaps w a b)
    (p : B.ι) (q : A.ι) {W : X.Opens} (hp : W ≤ B.U p) (hq : W ≤ A.U q) :
    resG X hp (b.f p) = resG X (le_inf hp hq)
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X hq (a.f q) := by
  have := congrArg (resG X (le_inf hp hq)) (h (p, q))
  rwa [map_mul, resG_resG, resG_resG] at this

theorem secMaps_genSec_iff {A B : LB X} (w : LB.Iso A B) (a : A.Gen) (ha : a.IsGen) (b : B.Gen)
    (hb : b.IsGen) :
    SecMaps w ⟨fun i => (a.s i).val, fun i j => congrArg Units.val (ha i j)⟩
      ⟨fun i => (b.s i).val, fun i j => congrArg Units.val (hb i j)⟩ ↔ LB.Gen.Maps w a b :=
  forall_congr' fun _ => ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩

theorem SecMaps.isGen {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec} (h : SecMaps w a b)
    (ha : IsRegularSec a) : w.IsGen := by
  rintro ⟨p, q⟩ ⟨p', q'⟩
  have hp : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
  have hq : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
  have hp' : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ B.U p' := inf_le_right.trans inf_le_left
  have hq' : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))) *
      res (le_inf hq hq') (A.g q q') = res (le_inf hp hp') (B.g p p') *
        res (le_inf hp' hq') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q'))) := by
    refine Units.ext (((ha q').resG hq').mul_right_cancel ?_)
    simp only [Units.val_mul, val_res]
    rw [mul_assoc, mul_assoc, ← sec_compat a q q' hq hq', ← h.on p' q' hp' hq', ← h.on p q hp hq,
      ← sec_compat b p p' hp hp']
  change res (le_inf hp hq) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))) =
    res (le_inf hp hp') (B.g p p') * (res (le_inf hq hq') (A.g q q'))⁻¹ *
      res (le_inf hp' hq') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

theorem SecMaps.unique {A B : LB X} {w w' : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : SecMaps w a b) (h' : SecMaps w' a b) (ha : IsRegularSec a) : w = w' := by
  obtain ⟨w⟩ := w
  obtain ⟨w'⟩ := w'
  congr 1
  funext p
  exact Units.ext (((ha p.2).resG inf_le_right).mul_right_cancel ((h p).symm.trans (h' p)))

theorem SecMaps.eq {A B : LB X} (hA : A.IsLB) {w : LB.Iso A B} {a : A.Sec} {b b' : B.Sec}
    (h : SecMaps w a b) (h' : SecMaps w a b') : b = b' :=
  sec_ext fun p => ext_germ fun x hx => by
    obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
    have hm : x ∈ B.U p ⊓ A.U q := ⟨hx, hq⟩
    have := congrArg (X.presheaf.germ (B.U p ⊓ A.U q) x hm).hom
      ((h (p, q)).trans (h' (p, q)).symm)
    rwa [germ_resG, germ_resG] at this

theorem SecMaps.isRegularSec {A B : LB X} (hA : A.IsLB) {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : SecMaps w a b) (ha : IsRegularSec a) : IsRegularSec b := fun p =>
  isRegularFn_of_locally fun x hx => by
    obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
    refine ⟨B.U p ⊓ A.U q, inf_le_left, ⟨hx, hq⟩, ?_⟩
    rw [h (p, q)]
    exact (IsRegularFn.of_isUnit (Units.isUnit _)).mul ((ha q).resG _)

theorem existsUnique_secMaps {A B : LB X} {a : A.Sec} {b : B.Sec} (ha : IsRegularSec a)
    (h : ∀ (p : B.ι) (q : A.ι), Associated (resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) (b.f p))) :
    ∃! w : LB.Iso A B, w.IsGen ∧ SecMaps w a b := by
  choose u hu using h
  let w : LB.Iso A B := ⟨fun p => u p.1 p.2⟩
  have hw : SecMaps w a b := fun p => ((mul_comm _ _).trans (hu p.1 p.2)).symm
  exact ⟨w, ⟨hw.isGen ha, hw⟩, fun w' hw' => hw'.2.unique hw ha⟩

theorem mem_nonzeroLocus_iff {L : LB X} (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i) :
    x ∈ Out.nonzeroLocus s ↔ x ∈ X.basicOpen (s.f i) := by
  refine ⟨fun h => ?_, fun h => Opens.mem_iSup.2 ⟨i, h⟩⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  have hxj : x ∈ L.U j := X.basicOpen_le _ hj
  have hm : x ∈ L.U i ⊓ L.U j := ⟨hx, hxj⟩
  have e := congrArg (X.presheaf.germ (L.U i ⊓ L.U j) x hm).hom (s.compat i j)
  rw [map_mul, germ_resG, germ_resG] at e
  rw [X.mem_basicOpen _ x hx]
  rw [X.mem_basicOpen _ x hxj] at hj
  exact (congrArg IsUnit e).mpr (((L.g i j).isUnit.map _).mul hj)

theorem SecMaps.nonzeroLocus_eq {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B}
    {a : A.Sec} {b : B.Sec} (h : SecMaps w a b) : Out.nonzeroLocus a = Out.nonzeroLocus b := by
  ext x
  obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
  obtain ⟨p, hp⟩ := LB.mem_of_cover hB x
  have hm : x ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  have e := congrArg (X.presheaf.germ (B.U p ⊓ A.U q) x hm).hom (h (p, q))
  rw [map_mul, germ_resG, germ_resG] at e
  refine (mem_nonzeroLocus_iff a q hq).trans (Iff.trans ?_ (mem_nonzeroLocus_iff b p hp).symm)
  rw [X.mem_basicOpen _ x hq, X.mem_basicOpen _ x hp]
  refine Iff.trans ?_ (iff_of_eq (congrArg IsUnit e)).symm
  rw [IsUnit.mul_iff]
  exact ⟨fun h => ⟨(Units.isUnit _).map _, h⟩, fun h => h.2⟩

theorem isRegularSec_of_ne_zero [IsIntegral X] {L : LB X} (s : L.Sec) {i : L.ι} (hi : s.f i ≠ 0) :
    IsRegularSec s := fun j => isRegularFn_iff_germ.2 fun x hx => by
  have hne : (L.U i : Set X).Nonempty := by
    by_contra h
    exact hi (ext_germ fun y hy => (h ⟨y, hy⟩).elim)
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (L.U i).isOpen (L.U j).isOpen hne ⟨x, hx⟩
  have hj : s.f j ≠ 0 := fun h0 => hi (germ_injective_of_isIntegral X y hy.1 (by
    have e := congrArg (X.presheaf.germ (L.U i ⊓ L.U j) y hy).hom (s.compat i j)
    rw [map_mul, germ_resG, germ_resG, h0, map_zero, mul_zero] at e
    exact e.trans (map_zero _).symm))
  exact isRegularFn_iff_germ.1 (isRegularFn_of_ne_zero hj) x hx

theorem pull_U (L : LB X) (φ : Y ⟶ X) (j : PUnit → L.ι) : (L.pull φ).U j = φ ⁻¹ᵁ L.U (j ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ => φ) j ⟨⟩) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_g (L : LB X) (φ : Y ⟶ X) (j j' : PUnit → L.ι) :
    (L.pull φ).g j j' = res (LB.wchart_inter_le L (fun _ => φ) j j' ⟨⟩)
      (pullU φ _ (L.g (j ⟨⟩) (j' ⟨⟩))) := by
  change LB.lcg L (fun _ : PUnit => φ) (fun _ => 1) j j' = _
  rw [LB.lcg, Fintype.prod_unique, zpow_one]

def secPull {L : LB X} (s : L.Sec) (φ : Y ⟶ X) : (L.pull φ).Sec where
  f j := resG Y (pull_U L φ j).le ((φ.app _).hom (s.f (j ⟨⟩)))
  compat j j' := by
    have e := congrArg (fun a => resG Y (LB.wchart_inter_le L (fun _ => φ) j j' ⟨⟩)
      ((φ.app _).hom a)) (s.compat (j ⟨⟩) (j' ⟨⟩))
    simp only [map_mul] at e
    rw [app_resG, app_resG, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    exact congrArg₂ (· * ·) (congrArg Units.val (pull_g L φ j j')).symm (resG_resG _ _ _).symm

theorem nonzeroLocus_secPull {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    Out.nonzeroLocus (secPull s φ) = φ ⁻¹ᵁ Out.nonzeroLocus s := by
  have key : ∀ j : PUnit → L.ι, Y.basicOpen ((secPull s φ).f j) = φ ⁻¹ᵁ X.basicOpen (s.f (j ⟨⟩)) := by
    intro j
    refine (Y.basicOpen_res _ (homOfLE (pull_U L φ j).le).op).trans ?_
    rw [Scheme.preimage_basicOpen]
    exact inf_eq_right.2 ((Y.basicOpen_le _).trans (pull_U L φ j).ge)
  ext y
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
    exact Opens.mem_iSup.2 ⟨j ⟨⟩, (key j).le hj⟩
  · intro h
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show φ y ∈ Out.nonzeroLocus s from h)
    exact Opens.mem_iSup.2 ⟨fun _ => i, (key fun _ => i).ge hi⟩

theorem lbPow_U (L : LB X) (n : ℕ) (j : PUnit → L.ι) : (lbPow L n).U j = L.U (j ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ => 𝟙 X) j ⟨⟩) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem lbPow_g (L : LB X) (n : ℕ) (j j' : PUnit → L.ι) :
    (lbPow L n).g j j' = res (inf_le_inf (lbPow_U L n j).le (lbPow_U L n j').le)
      (L.g (j ⟨⟩) (j' ⟨⟩)) ^ n := by
  change LB.lcg L (fun _ : PUnit => 𝟙 X) (fun _ => (n : ℤ)) j j' = _
  rw [LB.lcg, Fintype.prod_unique, zpow_natCast]
  rfl

def secPow {L : LB X} (s : L.Sec) (n : ℕ) : (lbPow L n).Sec where
  f j := resG X (lbPow_U L n j).le (s.f (j ⟨⟩)) ^ n
  compat j j' := by
    have e := sec_compat s (j ⟨⟩) (j' ⟨⟩) (inf_le_left.trans (lbPow_U L n j).le)
      (inf_le_right.trans (lbPow_U L n j').le)
    change resG X _ _ = _ * resG X _ _
    rw [map_pow, map_pow, resG_resG, resG_resG, e, mul_pow]
    exact congrArg (· * _) ((congrArg Units.val (lbPow_g L n j j')).trans
      (Units.val_pow_eq_pow_val _ _)).symm

theorem IsRegularSec.secPow {L : LB X} {s : L.Sec} (hs : IsRegularSec s) (n : ℕ) :
    IsRegularSec (secPow s n) := fun j => ((hs (j ⟨⟩)).resG _).pow n

section Rational

variable [IsIntegral X]

theorem genericPoint_mem (W : X.Opens) [h : Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)

theorem germK_resG {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (a : Γ(X, U)) :
    (X.germToFunctionField V).hom (resG X h a) = (X.germToFunctionField U).hom a :=
  germ_resG h _ _ a

theorem ext_germK {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ hU : genericPoint X ∈ U, (X.presheaf.germ U _ hU).hom a = (X.presheaf.germ U _ hU).hom b) :
    a = b := by
  by_cases hU : Nonempty U
  · exact germ_injective_of_isIntegral X _ (genericPoint_mem U) (h _)
  · exact ext_germ fun x hx => (hU ⟨⟨x, hx⟩⟩).elim

theorem exists_germK_eq_of_stalk (U : X.Opens) [Nonempty U] (t : X.functionField)
    (h : ∀ x ∈ U, t ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    ∃ a : Γ(X, U), (X.germToFunctionField U).hom a = t := by
  have loc : ∀ x : U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : x.1 ∈ V) (c : Γ(X, V)),
      ∀ hV : genericPoint X ∈ V, (X.presheaf.germ V _ hV).hom c = t := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr⟩ := h x hx
    obtain ⟨V, hV, c, rfl⟩ := X.presheaf.exists_germ_eq r
    have : Nonempty V := ⟨⟨x, hV⟩⟩
    refine ⟨U ⊓ V, inf_le_left, ⟨hx, hV⟩, resG X inf_le_right c, fun hV' => ?_⟩
    rw [germ_resG, ← hr]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField X hV c).symm
  choose V hV hx c hc using loc
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hV i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) c (fun i j => ext_germK fun hη =>
      ((germ_resG inf_le_left _ hη (c i)).trans (hc i _)).trans
        ((germ_resG inf_le_right _ hη (c j)).trans (hc j _)).symm)
  obtain ⟨x⟩ := ‹Nonempty U›
  have : Nonempty (V x) := ⟨⟨x.1, hx x⟩⟩
  refine ⟨s, ?_⟩
  rw [← hc x (genericPoint_mem _), ← hs x]
  exact (germ_resG (hV x) _ (genericPoint_mem _) s).symm

def ratSecs {L : LB X} (s : L.Sec) (V : X.Opens) [Nonempty V] :
    Submodule Γ(X, V) X.functionField where
  carrier := {h | ∀ (i : L.ι) [Nonempty (V ⊓ L.U i : X.Opens)], ∃ a : Γ(X, V ⊓ L.U i),
    (X.germToFunctionField _).hom a =
      (X.germToFunctionField (V ⊓ L.U i)).hom (resG X inf_le_right (s.f i)) * h}
  add_mem' := fun {h h'} hh hh' i _ => by
    obtain ⟨a, ha⟩ := hh i
    obtain ⟨a', ha'⟩ := hh' i
    exact ⟨a + a', by rw [map_add, ha, ha', mul_add]⟩
  zero_mem' := fun i _ => ⟨0, by rw [map_zero, mul_zero]⟩
  smul_mem' := fun c h hh i _ => by
    obtain ⟨a, ha⟩ := hh i
    refine ⟨resG X inf_le_left c * a, ?_⟩
    rw [map_mul, ha, germK_resG, Algebra.smul_def, mul_left_comm]
    rfl

theorem mem_ratSecs_iff_stalk {L : LB X} (s : L.Sec) (V : X.Opens) [Nonempty V]
    (h : X.functionField) :
    h ∈ ratSecs s V ↔ ∀ (i : L.ι) (x : X) (_ : x ∈ V) (hx : x ∈ L.U i),
      algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ _ x hx).hom (s.f i)) * h ∈
        Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  constructor
  · intro hh i x hxV hx
    have hm : x ∈ V ⊓ L.U i := ⟨hxV, hx⟩
    have : Nonempty (V ⊓ L.U i : X.Opens) := ⟨⟨x, hm⟩⟩
    obtain ⟨a, ha⟩ := hh i
    refine ⟨(X.presheaf.germ _ x hm).hom a, ?_⟩
    rw [← germ_resG (inf_le_right : V ⊓ L.U i ≤ L.U i) x hm]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField X hm a).trans (ha.trans
      (congrArg (· * h) (Scheme.algebraMap_germ_eq_germToFunctionField X hm _).symm))
  · intro hh i _
    refine exists_germK_eq_of_stalk _ _ fun x hx => ?_
    have := hh i x hx.1 hx.2
    rw [← germ_resG (inf_le_right : V ⊓ L.U i ≤ L.U i) x hx] at this
    exact (congrArg (fun r => r * h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField))
      (Scheme.algebraMap_germ_eq_germToFunctionField X hx _)).mp this

theorem SecMaps.ratSecs_eq {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} {a : A.Sec}
    {b : B.Sec} (hw : SecMaps w a b) (V : X.Opens) [Nonempty V] : ratSecs a V = ratSecs b V := by
  have key : ∀ (p : B.ι) (q : A.ι) (x : X) (hp : x ∈ B.U p) (hq : x ∈ A.U q),
      Associated ((X.presheaf.germ _ x hq).hom (a.f q)) ((X.presheaf.germ _ x hp).hom (b.f p)) := by
    intro p q x hp hq
    have hm : x ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
    have e := congrArg (X.presheaf.germ (B.U p ⊓ A.U q) x hm).hom (hw (p, q))
    rw [map_mul, germ_resG, germ_resG] at e
    exact (congrArg (Associated _) e).mpr
      (associated_unit_mul_right _ _ ((Units.isUnit _).map _))
  have mv : ∀ (x : X) (r r' : X.presheaf.stalk x) (h : X.functionField), r ∣ r' →
      algebraMap _ X.functionField r * h ∈ Set.range (algebraMap (X.presheaf.stalk x) _) →
      algebraMap _ X.functionField r' * h ∈ Set.range (algebraMap (X.presheaf.stalk x) _) := by
    rintro x r _ h ⟨c, rfl⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [map_mul, map_mul, hd]; ring⟩
  ext h
  rw [mem_ratSecs_iff_stalk, mem_ratSecs_iff_stalk]
  constructor
  · intro H p x hV hp
    obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
    exact mv x _ _ h (key p q x hp hq).dvd (H q x hV hq)
  · intro H q x hV hq
    obtain ⟨p, hp⟩ := LB.mem_of_cover hB x
    exact mv x _ _ h (key p q x hp hq).symm.dvd (H p x hV hp)

def genericChart {L : LB X} (hL : L.IsLB) : L.ι := (LB.mem_of_cover hL (genericPoint X)).choose

theorem mem_genericChart {L : LB X} (hL : L.IsLB) : genericPoint X ∈ L.U (genericChart hL) :=
  (LB.mem_of_cover hL (genericPoint X)).choose_spec

def ratOf {L : LB X} (hL : L.IsLB) (s : L.Sec) (V : X.Opens) [Nonempty V] :
    (∀ i, Γ(X, V ⊓ L.U i)) →+ X.functionField where
  toFun t := (X.presheaf.germ (V ⊓ L.U (genericChart hL)) (genericPoint X)
      ⟨genericPoint_mem V, mem_genericChart hL⟩).hom (t _) *
    (@id X.functionField
      ((X.presheaf.germ _ (genericPoint X) (mem_genericChart hL)).hom (s.f _)))⁻¹
  map_zero' := by rw [Pi.zero_apply, map_zero, zero_mul]
  map_add' t t' := by rw [Pi.add_apply, map_add, add_mul]

theorem ratOf_smul {L : LB X} (hL : L.IsLB) (s : L.Sec) (V : X.Opens) [Nonempty V] (c : Γ(X, V))
    (t : ∀ i, Γ(X, V ⊓ L.U i)) :
    ratOf hL s V (fun i => resG X inf_le_left c * t i) = c • ratOf hL s V t := by
  have hm : genericPoint X ∈ V ⊓ L.U (genericChart hL) :=
    ⟨genericPoint_mem V, mem_genericChart hL⟩
  change (X.presheaf.germ _ _ hm).hom (resG X inf_le_left c * t _) * _ = _
  rw [map_mul, germ_resG, mul_assoc]
  rfl

theorem germK_eq_mul_ratOf {L : LB X} (hL : L.IsLB) {s : L.Sec} (hs : IsRegularSec s)
    (V : X.Opens) [Nonempty V] {t : ∀ i, Γ(X, V ⊓ L.U i)} (ht : t ∈ secOn L V) (i : L.ι)
    [Nonempty (V ⊓ L.U i : X.Opens)] :
    (X.germToFunctionField _).hom (t i) =
      (X.germToFunctionField (V ⊓ L.U i)).hom (resG X inf_le_right (s.f i)) * ratOf hL s V t := by
  have hi : genericPoint X ∈ V ⊓ L.U i := genericPoint_mem _
  have h0 := mem_genericChart hL
  have hm : genericPoint X ∈ V ⊓ L.U i ⊓ L.U (genericChart hL) := ⟨hi, h0⟩
  have hm' : genericPoint X ∈ L.U i ⊓ L.U (genericChart hL) := ⟨hi.2, h0⟩
  have e₁ := congrArg (X.presheaf.germ _ _ hm).hom (ht i (genericChart hL))
  have e₂ := congrArg (X.presheaf.germ _ _ hm').hom (s.compat i (genericChart hL))
  rw [map_mul, germ_resG, germ_resG, germ_resG] at e₁
  rw [map_mul, germ_resG, germ_resG] at e₂
  have hne : @id X.functionField ((X.presheaf.germ _ _ h0).hom (s.f (genericChart hL))) ≠ 0 :=
    nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 (hs _) _ h0)
  have key : ∀ g a b : X.functionField, b ≠ 0 → g * a = g * b * (a * b⁻¹) := fun g a b hb => by
    field_simp
  refine e₁.trans ((key _ _ _ hne).trans ?_)
  exact congrArg (· * ratOf hL s V t) (e₂.symm.trans
    (germ_resG (inf_le_right : V ⊓ L.U i ≤ L.U i) _ hi (s.f i)).symm)

theorem bijOn_ratOf {L : LB X} (hL : L.IsLB) {s : L.Sec} (hs : IsRegularSec s) (V : X.Opens)
    [Nonempty V] : Set.BijOn (ratOf hL s V) (secOn L V) (ratSecs s V) := by
  refine ⟨fun t ht i _ => ⟨t i, germK_eq_mul_ratOf hL hs V ht i⟩, fun t ht t' ht' e => ?_,
    fun h hh => ?_⟩
  · funext i
    refine ext_germK fun hη => ?_
    have : Nonempty (V ⊓ L.U i : X.Opens) := ⟨⟨_, hη⟩⟩
    exact (germK_eq_mul_ratOf hL hs V ht i).trans
      ((congrArg _ e).trans (germK_eq_mul_ratOf hL hs V ht' i).symm)
  · have ex : ∀ i, ∃ a : Γ(X, V ⊓ L.U i), ∀ hη : genericPoint X ∈ V ⊓ L.U i,
        (X.presheaf.germ _ _ hη).hom a = (X.presheaf.germ _ _ hη.2).hom (s.f i) * h := by
      intro i
      by_cases hi : Nonempty (V ⊓ L.U i : X.Opens)
      · obtain ⟨a, ha⟩ := hh i
        exact ⟨a, fun hη => ha.trans (congrArg (· * h) (germ_resG _ _ hη _))⟩
      · exact ⟨0, fun hη => (hi ⟨⟨_, hη⟩⟩).elim⟩
    choose t ht using ex
    have hts : t ∈ secOn L V := fun i j => ext_germK fun hη => by
      have hm' : genericPoint X ∈ L.U i ⊓ L.U j := ⟨hη.1.2, hη.2⟩
      have e₂ := congrArg (X.presheaf.germ _ _ hm').hom (s.compat i j)
      rw [map_mul, germ_resG, germ_resG] at e₂
      rw [map_mul, germ_resG, germ_resG, germ_resG, ht, ht, ← mul_assoc]
      exact congrArg (· * h) e₂
    refine ⟨t, hts, ?_⟩
    have hm : genericPoint X ∈ V ⊓ L.U (genericChart hL) :=
      ⟨genericPoint_mem V, mem_genericChart hL⟩
    have hne : @id X.functionField
        ((X.presheaf.germ _ _ (mem_genericChart hL)).hom (s.f (genericChart hL))) ≠ 0 :=
      nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 (hs _) _ _)
    have key : ∀ b : X.functionField, b ≠ 0 → b * h * b⁻¹ = h := fun b hb => by field_simp
    exact (congrArg (· * _) (ht _ hm)).trans (key _ hne)

end Rational

theorem app_subschemeι_eq_zero_iff (J : Y.IdealSheafData) {V : Y.Opens} (b : Γ(Y, V)) :
    (J.subschemeι.app V).hom b = 0 ↔
      ∀ (W : Y.affineOpens) (h : W.1 ≤ V), resG Y h b ∈ J.ideal W := by
  have hk : ∀ W : Y.affineOpens, J.ideal W = RingHom.ker (J.subschemeι.app W.1).hom := fun W => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  constructor
  · intro hb W h
    rw [hk, RingHom.mem_ker, app_resG, hb, map_zero]
  · intro h
    refine ext_germ fun z hz => ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (a := J.subschemeι z) hz V.isOpen
    have hWV' : W ≤ V := hWV
    have := h ⟨W, hW⟩ hWV'
    rw [hk, RingHom.mem_ker, app_resG] at this
    rw [← germ_resG (J.subschemeι.preimage_mono hWV') z hzW, this, map_zero, map_zero]

theorem comap_le_iff (I : X.IdealSheafData) (φ : Y ⟶ X) (J : Y.IdealSheafData) :
    I.comap φ ≤ J ↔ ∀ (U : X.affineOpens), ∀ a ∈ I.ideal U, ∀ (W : Y.affineOpens)
      (h : W.1 ≤ φ ⁻¹ᵁ U.1), resG Y h ((φ.app U.1).hom a) ∈ J.ideal W := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map, Scheme.Hom.ker,
    Scheme.IdealSheafData.le_ofIdeals_iff]
  refine forall_congr' fun U => forall₂_congr fun a _ => ?_
  exact app_subschemeι_eq_zero_iff J ((φ.app U.1).hom a)

end GlobalTheory.Cartier
