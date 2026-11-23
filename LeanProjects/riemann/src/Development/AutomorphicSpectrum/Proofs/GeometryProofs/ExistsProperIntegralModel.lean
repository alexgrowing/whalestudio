import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClSch

open Polynomial HomogeneousLocalization

variable {Ω : Type} [Field Ω] (o : Type) [CommRing o] [Algebra o Ω] {κ : Type} (x : κ → Ω)

def coordSpan : Submodule o Ω := Submodule.span o (Set.range x)

def rees : Subalgebra o (Polynomial Ω) where
  carrier := {f | ∀ i, f.coeff i ∈ coordSpan o x ^ i}
  mul_mem' := by
    intro f g hf hg i
    rw [Set.mem_setOf_eq] at hf hg
    rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun ij hij => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hij, pow_add]
    exact Submodule.mul_mem_mul (hf _) (hg _)
  add_mem' := by
    intro f g hf hg i
    rw [Polynomial.coeff_add]
    exact Submodule.add_mem _ (hf i) (hg i)
  algebraMap_mem' := by
    intro r i
    rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [pow_zero]
      exact Submodule.algebraMap_mem r
    · exact Submodule.zero_mem _

def grading (n : ℕ) : Submodule o (rees o x) where
  carrier := {f | ∀ i, i ≠ n → (f : (Polynomial Ω)).coeff i = 0}
  add_mem' := by
    intro f g hf hg i hi
    simp [hf i hi, hg i hi]
  zero_mem' := by
    intro i _
    simp
  smul_mem' := by
    intro r f hf i hi
    have : ((r • f : rees o x) : (Polynomial Ω)) = r • (f : (Polynomial Ω)) := rfl
    rw [this, Polynomial.coeff_smul, hf i hi, smul_zero]

variable {o x}

lemma coe_eq_monomial {n : ℕ} {f : rees o x} (hf : f ∈ grading o x n) :
    (f : (Polynomial Ω)) = Polynomial.monomial n ((f : (Polynomial Ω)).coeff n) := by
  ext i
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hf i (Ne.symm h)

def comp (i : ℕ) (f : rees o x) : grading o x i :=
  ⟨⟨Polynomial.monomial i ((f : (Polynomial Ω)).coeff i), by
      intro k
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · rw [← h]
        exact f.2 _
      · exact Submodule.zero_mem _⟩, by
    intro k hk
    change (Polynomial.monomial i ((f : (Polynomial Ω)).coeff i)).coeff k = 0
    rw [Polynomial.coeff_monomial, if_neg (Ne.symm hk)]⟩

lemma coeff_coeAddMonoidHom (y : DirectSum ℕ fun i => grading o x i) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (grading o x) y : rees o x) : (Polynomial Ω)).coeff n =
      ((y n : rees o x) : (Polynomial Ω)).coeff n := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : i = n
    · subst h
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), a.2 n (Ne.symm h)]
      simp
  | add a b ha hb =>
    rw [map_add, DirectSum.add_apply]
    simp only [AddMemClass.coe_add, Subalgebra.coe_add, Polynomial.coeff_add, ha, hb]

lemma bijective_coeAddMonoidHom :
    Function.Bijective (DirectSum.coeAddMonoidHom (grading o x)) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    refine DFinsupp.ext fun n => ?_
    refine Subtype.ext (Subtype.ext ?_)
    have h1 := coeff_coeAddMonoidHom y n
    rw [hy] at h1
    rw [coe_eq_monomial (y n).2, ← h1]
    simp
  · intro f
    refine ⟨∑ i ∈ (f : (Polynomial Ω)).support, DirectSum.of (fun i => grading o x i) i (comp i f), ?_⟩
    rw [map_sum]
    refine Subtype.ext ?_
    simp only [DirectSum.coeAddMonoidHom_of]
    rw [AddSubmonoidClass.coe_finset_sum]
    exact (Polynomial.as_sum_support (f : (Polynomial Ω))).symm

instance gradedRing : GradedRing (grading o x) where
  one_mem := by
    intro i hi
    change (1 : (Polynomial Ω)).coeff i = 0
    rw [Polynomial.coeff_one, if_neg hi]
  mul_mem := by
    intro i j a b ha hb k hk
    change ((a : (Polynomial Ω)) * (b : (Polynomial Ω))).coeff k = 0
    rw [coe_eq_monomial ha, coe_eq_monomial hb, Polynomial.monomial_mul_monomial,
      Polynomial.coeff_monomial, if_neg (Ne.symm hk)]
  decompose' := (Equiv.ofBijective _ bijective_coeAddMonoidHom).symm
  left_inv := (Equiv.ofBijective _ bijective_coeAddMonoidHom).apply_symm_apply
  right_inv := (Equiv.ofBijective _ bijective_coeAddMonoidHom).symm_apply_apply

end GlobalTheory.CompanionTheory.Ar.ClSch

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClSch

open Polynomial HomogeneousLocalization

variable {Ω : Type} [Field Ω] {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

def ev : rees o x →+* Ω :=
  (Polynomial.evalRingHom (1 : Ω)).comp (rees o x).val.toRingHom

lemma ev_apply (f : rees o x) : ev f = (f : Polynomial Ω).eval 1 := rfl

lemma ev_of_mem {n : ℕ} {f : rees o x} (hf : f ∈ grading o x n) :
    ev f = (f : Polynomial Ω).coeff n := by
  rw [ev_apply, coe_eq_monomial hf, Polynomial.eval_monomial, one_pow, mul_one,
    Polynomial.coeff_monomial, if_pos rfl]

lemma eq_zero_of_ev {n : ℕ} {f : rees o x} (hf : f ∈ grading o x n) (h : ev f = 0) : f = 0 := by
  rw [ev_of_mem hf] at h
  refine Subtype.ext ?_
  rw [coe_eq_monomial hf, h]
  simp

def coord (c : κ) : rees o x :=
  ⟨Polynomial.monomial 1 (x c), by
    intro k
    rw [Polynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [pow_one]
      exact Submodule.subset_span ⟨c, rfl⟩
    · exact Submodule.zero_mem _⟩

lemma coord_mem (c : κ) : coord (o := o) (x := x) c ∈ grading o x 1 := by
  intro i hi
  change (Polynomial.monomial 1 (x c)).coeff i = 0
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]

lemma ev_coord (c : κ) : ev (coord (o := o) (x := x) c) = x c := by
  rw [ev_apply]
  change (Polynomial.monomial 1 (x c)).eval 1 = x c
  simp

def locVal (g : rees o x) (hu : IsUnit (ev g)) : Localization.Away g →+* Ω :=
  IsLocalization.Away.lift g hu

def chartVal (g : rees o x) (hu : IsUnit (ev g)) : Away (grading o x) g →+* Ω :=
  (locVal g hu).comp (algebraMap _ _)

lemma chartVal_mk {g : rees o x} (hu : IsUnit (ev g)) {d : ℕ} (hg : g ∈ grading o x d) (n : ℕ)
    (a : rees o x) (ha : a ∈ grading o x (n • d)) :
    chartVal g hu (Away.mk (grading o x) hg n a ha) * ev g ^ n = ev a := by
  have h1 : (Localization.mk a ⟨g ^ n, n, rfl⟩ : Localization.Away g) *
      algebraMap _ _ (g ^ n) = algebraMap _ _ a := by
    rw [Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (locVal g hu) h1
  rw [map_mul] at h2
  have h3 : ∀ b : rees o x, locVal g hu (algebraMap _ _ b) = ev b := fun b =>
    IsLocalization.Away.lift_eq g hu b
  rw [h3, h3, map_pow] at h2
  rw [← h2]
  simp only [chartVal, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]

lemma chartVal_injective {g : rees o x} (hu : IsUnit (ev g)) {d : ℕ} (hg : g ∈ grading o x d) :
    Function.Injective (chartVal g hu) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading o x) hg z
  have h1 := chartVal_mk hu hg n a ha
  rw [hz, zero_mul] at h1
  have h2 : a = 0 := eq_zero_of_ev ha h1.symm
  subst h2
  ext
  simp [Away.val_mk, Localization.mk_zero]

lemma chartVal_awayMap {f g y : rees o x} {d e : ℕ} (hf : f ∈ grading o x d)
    (hg : g ∈ grading o x e) (hy : y = f * g) (hu : IsUnit (ev f)) (hv : IsUnit (ev y))
    (z : Away (grading o x) f) :
    chartVal y hv (awayMap (grading o x) hg hy z) = chartVal f hu z := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading o x) hf z
  rw [awayMap_mk]
  have h1 := chartVal_mk hu hf n a ha
  have h2 := chartVal_mk hv (hy ▸ SetLike.mul_mem_graded hf hg) n (a * g ^ n)
    (by rw [smul_add]; exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg))
  have hgu : IsUnit (ev g) := by
    have : IsUnit (ev f * ev g) := by rw [← map_mul, ← hy]; exact hv
    exact isUnit_of_mul_isUnit_right this
  have hfu := (hu.mul hgu).pow n
  have hy' : ev y = ev f * ev g := by rw [hy, map_mul]
  rw [hy', mul_pow, map_mul, map_pow, ← h1] at h2
  rw [mul_pow] at hfu
  refine hfu.mul_right_cancel ?_
  rw [h2]
  ring

lemma div_pow_mem_adjoin {c : κ} (hc : x c ≠ 0) (n : ℕ) {v : Ω} (hv : v ∈ coordSpan o x ^ n) :
    v / x c ^ n ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  have hV : ∀ w ∈ coordSpan o x, w / x c ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      exact Algebra.subset_adjoin ⟨j, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_div]
      exact add_mem ha hb
    | smul r a _ ha =>
      rw [Algebra.smul_def, mul_div_assoc]
      exact mul_mem (Subalgebra.algebraMap_mem _ r) ha
  induction n generalizing v with
  | zero =>
    rw [pow_zero, Submodule.mem_one] at hv
    obtain ⟨r, rfl⟩ := hv
    simpa using Subalgebra.algebraMap_mem _ r
  | succ n ih =>
    rw [pow_succ] at hv
    induction hv using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      have : a * b / x c ^ (n + 1) = (a / x c ^ n) * (b / x c) := by
        rw [pow_succ]
        field_simp
      rw [this]
      exact mul_mem (ih ha) (hV b hb)
    | add a _ b _ ha hb =>
      rw [add_div]
      exact add_mem ha hb

lemma ev_mem_pow {n : ℕ} {a : rees o x} (ha : a ∈ grading o x n) : ev a ∈ coordSpan o x ^ n := by
  rw [ev_of_mem ha]
  exact a.2 n

lemma unit_coord {c : κ} (hc : x c ≠ 0) : IsUnit (ev (coord (o := o) (x := x) c)) := by
  rw [ev_coord]
  exact hc.isUnit

lemma algebraMap_mem_grading (r : o) : algebraMap o (rees o x) r ∈ grading o x 0 := by
  intro i hi
  change (algebraMap o (Polynomial Ω) r).coeff i = 0
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C, if_neg hi]

lemma ev_algebraMap (r : o) : ev (algebraMap o (rees o x) r) = algebraMap o Ω r := by
  rw [ev_apply]
  change (algebraMap o (Polynomial Ω) r).eval 1 = _
  rw [Polynomial.algebraMap_apply, Polynomial.eval_C]

lemma mem_adjoin_iff_mem_range {c : κ} (hc : x c ≠ 0) (a : Ω) :
    a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔
      a ∈ (chartVal (coord c) (unit_coord (o := o) hc)).range := by
  constructor
  · intro ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      refine ⟨Away.mk (grading o x) (coord_mem c) 1 (coord j) (by simpa using coord_mem j), ?_⟩
      have h1 := chartVal_mk (unit_coord (o := o) hc) (coord_mem c) 1 (coord j)
        (by simpa using coord_mem j)
      rw [ev_coord, ev_coord, pow_one] at h1
      change _ = x j / x c
      rw [eq_div_iff hc]
      exact h1
    | algebraMap r =>
      refine ⟨Away.mk (grading o x) (coord_mem c) 0 (algebraMap o (rees o x) r)
        (by simpa using algebraMap_mem_grading r), ?_⟩
      have h1 := chartVal_mk (unit_coord (o := o) hc) (coord_mem c) 0 (algebraMap o (rees o x) r)
        (by simpa using algebraMap_mem_grading r)
      rw [pow_zero, mul_one, ev_algebraMap] at h1
      exact h1
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  · rintro ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading o x) (coord_mem c) z
    have h1 := chartVal_mk (unit_coord (o := o) hc) (coord_mem c) n a ha
    rw [ev_coord] at h1
    have h2 : chartVal (coord c) (unit_coord (o := o) hc) (Away.mk (grading o x) (coord_mem c) n a ha)
        = ev a / x c ^ n := by
      rw [eq_div_iff (pow_ne_zero _ hc)]
      exact h1
    rw [h2]
    refine div_pow_mem_adjoin hc n ?_
    simpa using ev_mem_pow ha

lemma adjoin_coord_eq_top :
    Algebra.adjoin (grading o x 0) (Set.range fun c => coord (o := o) (x := x) c) = ⊤ := by
  set S := Algebra.adjoin (grading o x 0) (Set.range fun c => coord (o := o) (x := x) c) with hS
  let S' : Subring (Polynomial Ω) := S.toSubring.map (rees o x).val.toRingHom
  have hS' : ∀ s ∈ S, (s : Polynomial Ω) ∈ S' := fun s hs => ⟨s, hs, rfl⟩
  have hC : ∀ r : o, Polynomial.C (algebraMap o Ω r) ∈ S' := by
    intro r
    have h := hS' (algebraMap o (rees o x) r) (by
      have : algebraMap o (rees o x) r =
          algebraMap (grading o x 0) (rees o x) ⟨_, algebraMap_mem_grading r⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _)
    exact h
  have hV : ∀ w ∈ coordSpan o x, Polynomial.monomial 1 w ∈ S' := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      exact hS' (coord j) (Algebra.subset_adjoin ⟨j, rfl⟩)
    | zero => simpa using zero_mem S'
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | smul r a _ ha =>
      have : Polynomial.monomial 1 (r • a) =
          Polynomial.C (algebraMap o Ω r) * Polynomial.monomial 1 a := by
        rw [Algebra.smul_def, Polynomial.C_mul_monomial]
      rw [this]
      exact mul_mem (hC r) ha
  have hM : ∀ (n : ℕ) (v : Ω), v ∈ coordSpan o x ^ n → Polynomial.monomial n v ∈ S' := by
    intro n
    induction n with
    | zero =>
      intro v hv
      rw [pow_zero, Submodule.mem_one] at hv
      obtain ⟨r, rfl⟩ := hv
      simpa using hC r
    | succ n ih =>
      intro v hv
      rw [pow_succ] at hv
      induction hv using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
        have : Polynomial.monomial (n + 1) (a * b) =
            Polynomial.monomial n a * Polynomial.monomial 1 b := by
          rw [Polynomial.monomial_mul_monomial]
        rw [this]
        exact mul_mem (ih a ha) (hV b hb)
      | add a _ b _ ha hb =>
        rw [map_add]
        exact add_mem ha hb
  rw [eq_top_iff]
  intro f _
  have hf : (f : Polynomial Ω) ∈ S' := by
    rw [Polynomial.as_sum_support (f : Polynomial Ω)]
    exact sum_mem fun i _ => hM i _ (f.2 i)
  obtain ⟨s, hs, hsf⟩ := hf
  have : s = f := Subtype.ext hsf
  exact this ▸ hs

def zeroMap : o →+* grading o x 0 where
  toFun r := ⟨algebraMap o (rees o x) r, algebraMap_mem_grading r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

lemma zeroMap_surjective : Function.Surjective (zeroMap (o := o) (x := x)) := by
  rintro ⟨a, ha⟩
  have h0 : ev a ∈ coordSpan o x ^ 0 := ev_mem_pow ha
  rw [pow_zero, Submodule.mem_one] at h0
  obtain ⟨r, hr⟩ := h0
  refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := coe_eq_monomial ha
  rw [← ev_of_mem ha, ← hr] at h1
  change algebraMap o (Polynomial Ω) r = _
  rw [h1, Polynomial.algebraMap_apply]
  rfl

end GlobalTheory.CompanionTheory.Ar.ClSch

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.ClSch
open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {X : Scheme.{0}}

theorem genMap_toStalk {B : Type} [CommRing B] (θ : B →+* Ω) (p : Spec (.of B))
    (h : genPt (Spec.map (CommRingCat.ofHom θ)) ⤳ p) (b : B) :
    genMap (Spec.map (CommRingCat.ofHom θ)) ⟨p, h⟩ ((StructureSheaf.toStalk B p).hom b) = θ b := by
  have h1 := Scheme.germ_stalkClosedPointTo_Spec (R := .of B) (S := .of Ω) (CommRingCat.ofHom θ)
  have h4 : (Spec (.of B)).presheaf.germ ⊤ p trivial ≫ (Spec (.of B)).presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom θ)) =
      (Scheme.ΓSpecIso (.of B)).hom ≫ CommRingCat.ofHom θ := by
    refine Eq.trans ?_ h1
    exact TopCat.Presheaf.germ_stalkSpecializes_assoc (Spec (.of B)).presheaf (U := ⊤) (y := p) trivial h _
  have h5 := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (.of B)).inv.hom b)) h4
  have h6 : ((Scheme.ΓSpecIso (.of B)).hom ≫ CommRingCat.ofHom θ).hom
      ((Scheme.ΓSpecIso (.of B)).inv.hom b) = θ b := by
    simp
  exact h5.trans h6

theorem chart_stalk {B : Type} [CommRing B] (θ : B →+* Ω) (j : Spec (.of B) ⟶ X) [IsOpenImmersion j]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hξ : ξ = Spec.map (CommRingCat.ofHom θ) ≫ j)
    (p : Spec (.of B)) (h : genPt ξ ⤳ j p) :
    ∃ φ : B →+* X.presheaf.stalk (j p),
      (∀ b, genMap ξ ⟨j p, h⟩ (φ b) = θ b) ∧ (∀ s, s ∉ p.asIdeal → IsUnit (φ s)) ∧
      ∀ t, ∃ a s, s ∉ p.asIdeal ∧ t * φ s = φ a := by
  subst hξ
  have h' : genPt (Spec.map (CommRingCat.ofHom θ)) ⤳ p :=
    (j.isOpenEmbedding.isInducing.specializes_iff).1 h
  let e : X.presheaf.stalk (j p) ≅ (Spec (.of B)).presheaf.stalk p := asIso (j.stalkMap p)
  have key : X.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom θ) ≫ j) =
      j.stalkMap p ≫ (Spec (.of B)).presheaf.stalkSpecializes h' ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom θ)) := by
    rw [Scheme.stalkClosedPointTo_comp]
    exact Scheme.Hom.stalkSpecializes_stalkMap_assoc j _ _ h' _
  have hg : ∀ t, genMap (Spec.map (CommRingCat.ofHom θ) ≫ j) ⟨j p, h⟩ (e.inv.hom t) =
      genMap (Spec.map (CommRingCat.ofHom θ)) ⟨p, h'⟩ t := by
    intro t
    have h5 : genMap (Spec.map (CommRingCat.ofHom θ) ≫ j) ⟨j p, h⟩ (e.inv.hom t) =
        ((Spec (.of B)).presheaf.stalkSpecializes h' ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom θ))).hom
          ((j.stalkMap p).hom (e.inv.hom t)) := congrArg (fun k => k.hom (e.inv.hom t)) key
    have h6 : (j.stalkMap p).hom (e.inv.hom t) = t := by
      change (e.hom).hom (e.inv.hom t) = t
      simp
    rw [h6] at h5
    exact h5
  haveI : p.asIdeal.IsPrime := p.isPrime
  let p' : PrimeSpectrum.Top B := p
  haveI hloc : IsLocalization.AtPrime ((structurePresheafInCommRingCat B).stalk p') p'.asIdeal :=
    inferInstance
  refine ⟨(StructureSheaf.toStalk B p ≫ e.inv).hom, ?_, ?_, ?_⟩
  · intro b
    exact (hg _).trans (genMap_toStalk θ p h' b)
  · intro s hs
    have h1 := IsLocalization.map_units (M := p'.asIdeal.primeCompl)
      ((structurePresheafInCommRingCat B).stalk p') (⟨s, hs⟩ : p'.asIdeal.primeCompl)
    exact h1.map e.inv.hom
  · intro t
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := p'.asIdeal.primeCompl)
      (S := (structurePresheafInCommRingCat B).stalk p') ((j.stalkMap p).hom t)
    refine ⟨a, s.1, s.2, ?_⟩
    have h7 := congrArg e.inv.hom hs
    have h8 : e.inv.hom ((j.stalkMap p).hom t) = t := by
      change (e.inv).hom ((e.hom).hom t) = t
      simp
    have h9 : e.inv.hom ((j.stalkMap p).hom t) * e.inv.hom ((StructureSheaf.toStalk B p).hom s.1) =
        e.inv.hom ((StructureSheaf.toStalk B p).hom a) := (map_mul e.inv.hom _ _).symm.trans h7
    rw [h8] at h9
    exact h9

end GlobalTheory.CompanionTheory.Ar.ClSch

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.ClSch
open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {X : Scheme.{0}}

lemma spec_of_injective {B : Type} [CommRing B] (θ : B →+* Ω) (hθ : Function.Injective θ)
    (p : Spec (.of B)) : genPt (Spec.map (CommRingCat.ofHom θ)) ⤳ p := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  intro b hb
  have h1 : θ b ∈ (IsLocalRing.closedPoint Ω).asIdeal := hb
  have h2 : θ b = 0 := by
    by_contra h
    exact ((IsLocalRing.mem_maximalIdeal _).1 h1) (isUnit_iff_ne_zero.2 h)
  rw [(map_eq_zero_iff θ hθ).1 h2]
  exact Ideal.zero_mem _

theorem tie_of_charts (o : Type) [CommRing o] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (B : {c // x c ≠ 0} → Type) [∀ c, CommRing (B c)] (θ : ∀ c, B c →+* Ω)
    (j : ∀ c, Spec (.of (B c)) ⟶ X) [∀ c, IsOpenImmersion (j c)]
    (hinj : ∀ c, Function.Injective (θ c))
    (hrange : ∀ (c : {c // x c ≠ 0}) (a : Ω),
      a ∈ Algebra.adjoin o (Set.range fun i => x i / x c) ↔ a ∈ (θ c).range)
    (hξ : ∀ c, ξ = Spec.map (CommRingCat.ofHom (θ c)) ≫ j c)
    (hcover : ∀ q : X, ∃ c p, j c p = q)
    (hover : ∀ (c d : {c // x c ≠ 0}) (p : Spec (.of (B d))) (s : B d),
      θ d s = x c / x d → s ∉ p.asIdeal → ∃ p', j c p' = j d p)
    (c₀ : {c // x c ≠ 0})
    (hfrac : ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun i => x i / x c₀),
      ∃ h ∈ Algebra.adjoin o (Set.range fun i => x i / x c₀), h ≠ 0 ∧ a = g / h) :
    CoordTie o ξ x ∧ (∀ q : X, genPt ξ ⤳ q) ∧ IsIntegral X := by
  have spec : ∀ c (p : Spec (.of (B c))), genPt ξ ⤳ j c p := by
    intro c p
    have h1 := spec_of_injective (θ c) (hinj c) p
    have h2 := h1.map (j c).continuous
    rw [hξ c]
    exact h2
  have spec' : ∀ q : X, genPt ξ ⤳ q := by
    intro q
    obtain ⟨c, p, rfl⟩ := hcover q
    exact spec c p
  have reg1 : ∀ c p b, θ c b ∈ regAt ξ ⟨j c p, spec c p⟩ := by
    intro c p b
    obtain ⟨φ, h1, -, -⟩ := chart_stalk (θ c) (j c) ξ (hξ c) p (spec c p)
    exact ⟨φ b, h1 b⟩
  have reg2 : ∀ c p a, a ∈ regAt ξ ⟨j c p, spec c p⟩ →
      ∃ u s, s ∉ p.asIdeal ∧ a * θ c s = θ c u := by
    intro c p a ha
    obtain ⟨φ, h1, -, h3⟩ := chart_stalk (θ c) (j c) ξ (hξ c) p (spec c p)
    obtain ⟨t, rfl⟩ := ha
    obtain ⟨u, s, hs, hts⟩ := h3 t
    refine ⟨u, s, hs, ?_⟩
    rw [← h1, ← h1, ← map_mul, hts]
  have inj : ∀ q : Cpt ξ, Function.Injective (genMap ξ q) := by
    rintro ⟨q, hq⟩
    obtain ⟨c, p, rfl⟩ := hcover q
    obtain ⟨φ, h1, h2, h3⟩ := chart_stalk (θ c) (j c) ξ (hξ c) p hq
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨u, s, hs, hts⟩ := h3 t
    have h4 := congrArg (genMap ξ ⟨j c p, hq⟩) hts
    rw [map_mul, ht, zero_mul, h1] at h4
    have h5 : u = 0 := (map_eq_zero_iff (θ c) (hinj c)).1 h4.symm
    rw [h5, map_zero] at hts
    exact (h2 s hs).mul_left_eq_zero.1 hts
  have chart1 : ∀ (c : {c // x c ≠ 0}) p, InChart ξ x c.1 ⟨j c p, spec c p⟩ := by
    intro c p
    refine ⟨c.2, fun c' => ?_⟩
    obtain ⟨b, hb⟩ := (hrange c _).1 (Algebra.subset_adjoin ⟨c', rfl⟩ :
      x c' / x c ∈ Algebra.adjoin o (Set.range fun i => x i / x c))
    rw [← hb]
    exact reg1 c p b
  have chart2 : ∀ (c : {c // x c ≠ 0}) (q : X) (hq : genPt ξ ⤳ q), InChart ξ x c.1 ⟨q, hq⟩ →
      ∃ p, j c p = q := by
    intro c q hq hch
    obtain ⟨d, p, rfl⟩ := hcover q
    obtain ⟨s, hs⟩ := (hrange d _).1 (Algebra.subset_adjoin ⟨c.1, rfl⟩ :
      x c / x d ∈ Algebra.adjoin o (Set.range fun i => x i / x d))
    refine hover c d p s hs ?_
    obtain ⟨u, s', hs', hu⟩ := reg2 d p _ (hch.2 d.1)
    intro hsp
    refine hs' ?_
    have h1 : θ d (s * u) = θ d s' := by
      rw [map_mul, hs, ← hu]
      have hc : x c ≠ 0 := c.2
      have hd : x d ≠ 0 := d.2
      field_simp
    rw [← hinj d h1]
    exact Ideal.mul_mem_right _ _ hsp
  have gen : IsCptGen ξ := by
    have h0 : genMap ξ ⟨genPt ξ, specializes_rfl⟩ = (Scheme.stalkClosedPointTo ξ).hom := by
      have h01 : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
          Scheme.stalkClosedPointTo ξ = Scheme.stalkClosedPointTo ξ :=
        (congrArg (· ≫ Scheme.stalkClosedPointTo ξ)
          (TopCat.Presheaf.stalkSpecializes_refl X.presheaf (genPt ξ))).trans (Category.id_comp _)
      exact congrArg (fun k => k.hom) h01
    refine ⟨⟨?_, ?_⟩, inj⟩
    · rw [← h0]
      exact inj _
    · intro a
      obtain ⟨g, hg, h, hh, hne, rfl⟩ := hfrac a
      obtain ⟨g', rfl⟩ := (hrange c₀ _).1 hg
      obtain ⟨h', rfl⟩ := (hrange c₀ _).1 hh
      let p : Spec (.of (B c₀)) := Spec.map (CommRingCat.ofHom (θ c₀)) (IsLocalRing.closedPoint Ω)
      obtain ⟨φ, h1, -, -⟩ := chart_stalk (θ c₀) (j c₀) ξ (hξ c₀) p (spec c₀ p)
      let w : B c₀ → X.presheaf.stalk (genPt ξ) :=
        fun b => (X.presheaf.stalkSpecializes (spec c₀ p)).hom (φ b)
      let f : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
      haveI : IsLocalHom f := Scheme.isLocalHom_stalkClosedPointTo' ξ
      have hw : ∀ b, f (w b) = θ c₀ b := h1
      have hu : IsUnit (w h') := by
        refine isUnit_of_map_unit f _ ?_
        rw [hw]
        exact isUnit_iff_ne_zero.2 hne
      obtain ⟨v, hv⟩ := hu
      refine ⟨w g' * (↑v⁻¹ : X.presheaf.stalk (genPt ξ)), ?_⟩
      change f (w g' * (↑v⁻¹ : X.presheaf.stalk (genPt ξ))) = _
      rw [map_mul, hw, eq_div_iff hne, mul_assoc, ← hw h', ← hv, ← map_mul, Units.inv_mul, map_one,
        mul_one]
  refine ⟨⟨gen, ?_, ?_, ?_⟩, spec', ?_⟩
  · rintro ⟨q, hq⟩
    obtain ⟨c, p, rfl⟩ := hcover q
    exact ⟨c.1, chart1 c p⟩
  · intro c hc
    refine ⟨(j ⟨c, hc⟩).opensRange, isAffineOpen_opensRange _, fun q => ⟨?_, ?_⟩⟩
    · rintro ⟨p, rfl⟩
      exact ⟨spec ⟨c, hc⟩ p, chart1 ⟨c, hc⟩ p⟩
    · rintro ⟨hq, hch⟩
      obtain ⟨p, hp⟩ := chart2 ⟨c, hc⟩ q hq hch
      exact ⟨p, hp⟩
  · intro c hc a
    constructor
    · rintro ha ⟨q, hq⟩ hch
      obtain ⟨b, rfl⟩ := (hrange ⟨c, hc⟩ a).1 ha
      obtain ⟨p, rfl⟩ := chart2 ⟨c, hc⟩ q hq hch
      exact reg1 ⟨c, hc⟩ p b
    · intro ha
      refine (hrange ⟨c, hc⟩ a).2 ?_
      let J : Ideal (B ⟨c, hc⟩) :=
        { carrier := {b | θ ⟨c, hc⟩ b * a ∈ (θ ⟨c, hc⟩).range}
          add_mem' := by
            intro b b' hb hb'
            rw [Set.mem_setOf_eq, map_add, add_mul]
            exact add_mem hb hb'
          zero_mem' := by
            rw [Set.mem_setOf_eq, map_zero, zero_mul]
            exact zero_mem _
          smul_mem' := by
            intro r b hb
            rw [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc]
            exact mul_mem ⟨r, rfl⟩ hb }
      have hJ : J = ⊤ := by
        by_contra hne
        obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
        let p : Spec (.of (B ⟨c, hc⟩)) := ⟨m, hm.isPrime⟩
        obtain ⟨u, s, hs, hu⟩ := reg2 ⟨c, hc⟩ p a (ha _ (chart1 ⟨c, hc⟩ p))
        refine hs (hJm ?_)
        have h3 : θ ⟨c, hc⟩ s * a ∈ (θ ⟨c, hc⟩).range := by
          rw [mul_comm, hu]
          exact ⟨u, rfl⟩
        exact h3
      have h1 : (1 : B ⟨c, hc⟩) ∈ J := hJ ▸ Submodule.mem_top
      have h2 : θ ⟨c, hc⟩ 1 * a ∈ (θ ⟨c, hc⟩).range := h1
      rwa [map_one, one_mul] at h2
  · haveI : Nonempty X := ⟨genPt ξ⟩
    haveI : IrreducibleSpace X := by
      have h1 : closure {genPt ξ} = (Set.univ : Set X) :=
        Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (spec' q)
      have h2 := (isIrreducible_singleton (x := genPt ξ)).closure
      rw [h1] at h2
      haveI : PreirreducibleSpace X := ⟨h2.2⟩
      exact ⟨inferInstance⟩
    haveI : ∀ q : X, _root_.IsReduced (X.presheaf.stalk q) := fun q =>
      isReduced_of_injective (genMap ξ ⟨q, spec' q⟩) (inj _)
    haveI : IsReduced X := isReduced_of_isReduced_stalk X
    exact isIntegral_of_irreducibleSpace_of_isReduced X

end GlobalTheory.CompanionTheory.Ar.ClSch

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.ClSch
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {Ω : Type} [Field Ω] {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

lemma specMap_chartVal_awayι {f g y : rees o x} {d e : ℕ} (hf : f ∈ grading o x d) (hd : 0 < d)
    (hg : g ∈ grading o x e) (hy : y = f * g) (hu : IsUnit (ev f)) (hv : IsUnit (ev y)) :
    Spec.map (CommRingCat.ofHom (chartVal f hu)) ≫ Proj.awayι (grading o x) f hf hd =
      Spec.map (CommRingCat.ofHom (chartVal y hv)) ≫ Proj.awayι (grading o x) y
        (hy ▸ SetLike.mul_mem_graded hf hg) (hd.trans_le (d.le_add_right e)) := by
  rw [← Proj.SpecMap_awayMap_awayι (grading o x) hf hd hg hy, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp]
  congr 3
  ext z
  exact (chartVal_awayMap hf hg hy hu hv z).symm

lemma chart_compat {c d : κ} (hc : x c ≠ 0) (hd : x d ≠ 0) :
    Spec.map (CommRingCat.ofHom (chartVal (coord (o := o) (x := x) c) (unit_coord hc))) ≫
        Proj.awayι (grading o x) (coord c) (coord_mem c) one_pos =
      Spec.map (CommRingCat.ofHom (chartVal (coord (o := o) (x := x) d) (unit_coord hd))) ≫
        Proj.awayι (grading o x) (coord d) (coord_mem d) one_pos := by
  have hv : IsUnit (ev (coord (o := o) (x := x) c * coord d)) := by
    rw [map_mul]
    exact (unit_coord hc).mul (unit_coord hd)
  rw [specMap_chartVal_awayι (coord_mem c) one_pos (coord_mem d) rfl (unit_coord hc) hv,
    specMap_chartVal_awayι (coord_mem d) one_pos (coord_mem c) (mul_comm _ _) (unit_coord hd) hv]

lemma exists_chart_point (q : Proj (grading o x)) :
    ∃ (c : κ) (hc : x c ≠ 0) (p : Spec (.of (Away (grading o x) (coord (o := o) (x := x) c)))),
      Proj.awayι (grading o x) (coord c) (coord_mem c) one_pos p = q := by
  have h1 := Proj.iSup_basicOpen_eq_top' (grading o x) (fun c => coord (o := o) (x := x) c)
    (fun c => ⟨1, coord_mem c⟩) adjoin_coord_eq_top
  have h2 : q ∈ (⊤ : (Proj (grading o x)).Opens) := trivial
  rw [← h1, TopologicalSpace.Opens.mem_iSup] at h2
  obtain ⟨c, hc⟩ := h2
  have hxc : x c ≠ 0 := by
    intro h0
    have h3 : coord (o := o) (x := x) c = 0 := by
      refine Subtype.ext ?_
      change Polynomial.monomial 1 (x c) = 0
      rw [h0, map_zero]
    rw [h3, Proj.basicOpen_zero] at hc
    exact hc
  rw [← Proj.opensRange_awayι (grading o x) _ (coord_mem c) one_pos] at hc
  obtain ⟨p, hp⟩ := hc
  exact ⟨c, hxc, p, hp⟩

lemma chart_overlap {c d : κ} (hc : x c ≠ 0) (hd : x d ≠ 0)
    (p : Spec (.of (Away (grading o x) (coord (o := o) (x := x) d))))
    (s : Away (grading o x) (coord (o := o) (x := x) d))
    (hs : chartVal (coord d) (unit_coord hd) s = x c / x d) (hp : s ∉ p.asIdeal) :
    ∃ p', Proj.awayι (grading o x) (coord c) (coord_mem c) one_pos p' =
      Proj.awayι (grading o x) (coord d) (coord_mem d) one_pos p := by
  have h1 := Proj.awayι_preimage_basicOpen (grading o x) (coord_mem (o := o) (x := x) d) one_pos
    (coord_mem c) one_pos
  have h2 : s = Away.isLocalizationElem (coord_mem (o := o) (x := x) d) (coord_mem c) := by
    refine chartVal_injective (unit_coord hd) (coord_mem d) ?_
    have h3 := chartVal_mk (unit_coord (o := o) hd) (coord_mem d) 1 (coord c ^ 1)
      (by simpa using coord_mem c)
    have e1 : ev (coord (o := o) (x := x) d) ^ 1 = x d := by rw [ev_coord, pow_one]
    have e2 : ev (coord (o := o) (x := x) c ^ 1) = x c := by rw [pow_one, ev_coord]
    rw [e1, e2] at h3
    rw [hs, div_eq_iff hd]
    exact h3.symm
  have h4 : p ∈ PrimeSpectrum.basicOpen
      (Away.isLocalizationElem (coord_mem (o := o) (x := x) d) (coord_mem c)) := by
    rw [← h2]
    exact hp
  rw [← h1] at h4
  have h5 : Proj.awayι (grading o x) (coord d) (coord_mem d) one_pos p ∈
      Proj.basicOpen (grading o x) (coord c) := h4
  rw [← Proj.opensRange_awayι (grading o x) _ (coord_mem c) one_pos] at h5
  exact h5

lemma chartVal_fromZero {g : rees o x} (hu : IsUnit (ev g)) (a : grading o x 0) :
    chartVal g hu (fromZeroRingHom (grading o x) _ a) = ev (a : rees o x) := by
  have h : (fromZeroRingHom (grading o x) (Submonoid.powers g) a).val =
      algebraMap (rees o x) (Localization.Away g) a := by
    simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
    exact Localization.mk_one_eq_algebraMap _
  change locVal g hu (fromZeroRingHom (grading o x) _ a).val = _
  rw [h]
  exact IsLocalization.Away.lift_eq g hu _

instance finiteType_grading [Finite κ] : Algebra.FiniteType (grading o x 0) (rees o x) :=
  ⟨Subalgebra.fg_def.2 ⟨_, Set.finite_range _, adjoin_coord_eq_top⟩⟩

end GlobalTheory.CompanionTheory.Ar.ClSch

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits ClSch HomogeneousLocalization

theorem exists_cl_scheme : ∀ (Ω : Type) [Field Ω] (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → ∃ (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of o)), CoordTie o ξ x ∧ (∀ q : X, genPt ξ ⤳ q) ∧ IsIntegral X ∧ IsProper s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap o Ω)) := by
  intro Ω _ o _ _ κ _ x c₀ hc₀ hfrac
  let B : {c // x c ≠ 0} → Type := fun c => Away (grading o x) (coord (o := o) (x := x) c.1)
  let θ : ∀ c : {c // x c ≠ 0}, B c →+* Ω := fun c => chartVal (coord c.1) (unit_coord c.2)
  let j : ∀ c : {c // x c ≠ 0}, Spec (.of (B c)) ⟶ Proj (grading o x) :=
    fun c => Proj.awayι (grading o x) (coord c.1) (coord_mem c.1) one_pos
  haveI : ∀ c, IsOpenImmersion (j c) := fun c => by dsimp only [j]; infer_instance
  let ξ : Spec (CommRingCat.of Ω) ⟶ Proj (grading o x) :=
    Spec.map (CommRingCat.ofHom (θ ⟨c₀, hc₀⟩)) ≫ j ⟨c₀, hc₀⟩
  have hξ : ∀ c, ξ = Spec.map (CommRingCat.ofHom (θ c)) ≫ j c := fun c => chart_compat hc₀ c.2
  obtain ⟨h1, h2, h3⟩ := tie_of_charts o x ξ B θ j
    (fun c => chartVal_injective _ (coord_mem c.1))
    (fun c a => mem_adjoin_iff_mem_range c.2 a) hξ
    (fun q => by
      obtain ⟨c, hc, p, hp⟩ := exists_chart_point q
      exact ⟨⟨c, hc⟩, p, hp⟩)
    (fun c d p s hs hp => chart_overlap c.2 d.2 p s hs hp)
    ⟨c₀, hc₀⟩ hfrac
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (zeroMap (o := o) (x := x)))) :=
    IsClosedImmersion.spec_of_surjective _ zeroMap_surjective
  refine ⟨Proj (grading o x), ξ,
    Proj.toSpecZero (grading o x) ≫ Spec.map (CommRingCat.ofHom (zeroMap (o := o) (x := x))),
    h1, h2, h3, inferInstance, ?_⟩
  have h4 : ξ ≫ Proj.toSpecZero (grading o x) =
      Spec.map (CommRingCat.ofHom (θ ⟨c₀, hc₀⟩)) ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom (grading o x) _)) := by
    simp only [ξ, j, Category.assoc, Proj.awayι_toSpecZero]
  rw [← Category.assoc, h4, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact (chartVal_fromZero (unit_coord hc₀) (zeroMap r)).trans (ev_algebraMap r)

end GlobalTheory.CompanionTheory.Ar
