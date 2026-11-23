import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameCharacterTorusValues

noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.isInt (x : _root_.Formalism.CyclotomicNorms.Fbar g) : IsIntegral (ZMod g) x :=
  Algebra.IsIntegral.isIntegral x

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar {f : (ZMod g)[X]} (hf : f ≠ 0) {x : _root_.Formalism.CyclotomicNorms.Fbar g} :
    x ∈ _root_.Formalism.CyclotomicNorms.rootsBar f ↔ aeval x f = 0 := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, aeval_def]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.nodup_minpoly (x : _root_.Formalism.CyclotomicNorms.Fbar g) : (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) x)).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  exact nodup_roots ((PerfectField.separable_of_irreducible
    (minpoly.irreducible (_root_.GlobalTheory.GoodCharsCompare.isInt x))).map)

theorem rootsBar_mul {f h : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0) :
    rootsBar (f * h) = rootsBar f + rootsBar h := by
  rw [rootsBar, rootsBar, rootsBar, Polynomial.map_mul, roots_mul]
  exact mul_ne_zero (Polynomial.map_ne_zero hf) (Polynomial.map_ne_zero hh)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_of_rootsBar {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : _root_.Formalism.CyclotomicNorms.rootsBar f = _root_.Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  have key : ∀ {p : (ZMod g)[X]}, p.Monic →
      ((_root_.Formalism.CyclotomicNorms.rootsBar p).map fun a => X - C a).prod = p.map (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)) := by
    intro p hp
    unfold _root_.Formalism.CyclotomicNorms.rootsBar
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      IsAlgClosed.card_roots_eq_natDegree
  apply Polynomial.map_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g))
    (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective
  rw [← key hf, ← key hh, e]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.card_rootsBar (f : (ZMod g)[X]) :
    (_root_.Formalism.CyclotomicNorms.rootsBar f).card = f.natDegree := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem exists_minpoly {P : (ZMod g)[X]} (hm : P.Monic) (hP : Irreducible P) :
    ∃ x : Fbar g, P = minpoly (ZMod g) x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) P (degree_pos_of_irreducible hP).ne'
  exact ⟨x, minpoly.eq_of_irreducible_of_monic hP hx hm⟩

abbrev dg (y : Fbar g) : ℕ := (minpoly (ZMod g) y).natDegree

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.dg_pos (y : _root_.Formalism.CyclotomicNorms.Fbar g) : 0 < _root_.GlobalTheory.GoodCharsCompare.dg y :=
  minpoly.natDegree_pos (_root_.GlobalTheory.GoodCharsCompare.isInt y)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar (y : _root_.Formalism.CyclotomicNorms.Fbar g) :
    y ^ g ^ _root_.GlobalTheory.GoodCharsCompare.dg y = y ∧
    ∀ i < _root_.GlobalTheory.GoodCharsCompare.dg y, ∀ j < _root_.GlobalTheory.GoodCharsCompare.dg y,
      y ^ g ^ i = y ^ g ^ j → i = j := by
  have hg : g.Prime := Fact.out
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {y}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {y}) := Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) {y}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {y}) =
      g ^ _root_.GlobalTheory.GoodCharsCompare.dg y := by
    rw [Module.card_eq_pow_finrank (K := ZMod g) (V := IntermediateField.adjoin (ZMod g) {y}),
      ZMod.card, IntermediateField.adjoin.finrank hint]
  have fixed : ∀ k, 0 < k → y ^ g ^ k = y → _root_.GlobalTheory.GoodCharsCompare.dg y ≤ k := by
    intro k hk hy
    let S : Subfield (_root_.Formalism.CyclotomicNorms.Fbar g) :=
      (iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k).eqLocusField (RingHom.id _)
    let T : IntermediateField (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) := S.toIntermediateField (fun x => by
      show iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) x) =
        algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) x
      rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow])
    have hKT : IntermediateField.adjoin (ZMod g) {y} ≤ T :=
      IntermediateField.adjoin_simple_le_iff.mpr (by
        show iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k y = y
        rw [iterateFrobenius_def, hy])
    have hne : (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero _ hk.ne' hg.one_lt
    have hle : Fintype.card (IntermediateField.adjoin (ZMod g) {y}) ≤ g ^ k := by
      classical
      calc Fintype.card (IntermediateField.adjoin (ZMod g) {y})
          = (Finset.univ.image fun z : IntermediateField.adjoin (ZMod g) {y} =>
              (z : _root_.Formalism.CyclotomicNorms.Fbar g)).card := by
            rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).roots.toFinset.card := by
            apply Finset.card_le_card
            intro z hz
            obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
            have hw : (w : _root_.Formalism.CyclotomicNorms.Fbar g) ^ g ^ k = w := by
              rw [← iterateFrobenius_def]
              exact hKT w.2
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hw,
              sub_self]
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).roots.card := Multiset.toFinset_card_le _
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).natDegree := card_roots' _
        _ = g ^ k := FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hk.ne' hg.one_lt
    rw [hcard] at hle
    exact (Nat.pow_le_pow_iff_right hg.one_lt).mp hle
  refine ⟨?_, ?_⟩
  · have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) y)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  · have key : ∀ i j, i < j → j < _root_.GlobalTheory.GoodCharsCompare.dg y → y ^ g ^ i = y ^ g ^ j → False := by
      intro i j hij hj e
      have hfix : y ^ g ^ (j - i) = y := by
        apply (iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g i).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add,
          Nat.sub_add_cancel hij.le]
        exact e.symm
      have := fixed (j - i) (Nat.sub_pos_of_lt hij) hfix
      omega
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj e).elim
    · exact h
    · exact (key j i h hi e.symm).elim

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g (f : (ZMod g)[X]) (y : _root_.Formalism.CyclotomicNorms.Fbar g) (i : ℕ)
    (h : aeval y f = 0) : aeval (y ^ g ^ i) f = 0 := by
  induction i with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, pow_mul, ← expand_aeval, ZMod.expand_card, map_pow, ih,
      zero_pow (Fact.out : g.Prime).ne_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
open Classical in
theorem _root_.GlobalTheory.GoodCharsCompare.roots_minpoly (y : _root_.Formalism.CyclotomicNorms.Fbar g) :
    (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y)).toFinset =
      (Finset.range (_root_.GlobalTheory.GoodCharsCompare.dg y)).image fun i => y ^ g ^ i := by
  have h0 : minpoly (ZMod g) y ≠ 0 := minpoly.ne_zero (_root_.GlobalTheory.GoodCharsCompare.isInt y)
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Multiset.mem_toFinset, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar h0]
    exact _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g _ _ _ (minpoly.aeval _ _)
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    · calc _ ≤ (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y)).card := Multiset.toFinset_card_le _
        _ = _ := _root_.GlobalTheory.GoodCharsCompare.card_rootsBar _
    · intro i hi j hj e
      exact (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 i (by simpa using hi) j
        (by simpa using hj) e

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.mem_roots_minpoly {y z : _root_.Formalism.CyclotomicNorms.Fbar g} :
    z ∈ _root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y) ↔ ∃ i, z = y ^ g ^ i := by
  classical
  constructor
  · intro hz
    rw [← Multiset.mem_toFinset, _root_.GlobalTheory.GoodCharsCompare.roots_minpoly] at hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar
      (minpoly.ne_zero (_root_.GlobalTheory.GoodCharsCompare.isInt y))]
    exact _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g _ _ _ (minpoly.aeval _ _)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.pow_g_of {y : _root_.Formalism.CyclotomicNorms.Fbar g} {d : ℕ} (h : y ^ (g ^ d - 1) = 1) :
    y ^ g ^ d = y := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow d g (Fact.out : g.Prime).pos), pow_succ, h, one_mul]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_sub_one_eq_one_of_pow_pow_eq {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.pow_dg {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) :
    y ^ (g ^ _root_.GlobalTheory.GoodCharsCompare.dg y - 1) = 1 :=
  pow_sub_one_eq_one_of_pow_pow_eq hy (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1

theorem exists_prim {d : ℕ} (hd : 0 < d) :
    ∃ (φ : GaloisField g d →ₐ[ZMod g] Fbar g) (u : GaloisField g d), IsPrimitiveRoot (φ u) (g ^ d - 1) := by
  let φ : GaloisField g d →ₐ[ZMod g] Fbar g := IsAlgClosed.lift
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField g d)ˣ)
  refine ⟨φ, u, IsPrimitiveRoot.map_of_injective ?_ φ.injective⟩
  rw [Nat.card_units, GaloisField.card g d hd.ne'] at hu
  rw [← hu, ← orderOf_units]
  exact IsPrimitiveRoot.orderOf _

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.rootC_prim {d : ℕ} (hd : 0 < d) :
    IsPrimitiveRoot (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1)) (g ^ d - 1) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC
  exact Complex.isPrimitiveRoot_exp _ (_root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos hd).ne'

theorem rootOfOne_eq (d m : ℕ) : rootOfOne g d m = rootC (g ^ d - 1) ^ m := by
  have : 1 ≤ g ^ d := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
  rw [rootOfOne, rootC, ← Complex.exp_nat_mul, Nat.cast_sub this]
  congr 1
  push_cast
  ring

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_log (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d)
    {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ^ (g ^ d - 1) = 1) :
    ∃ m, ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ m := by
  haveI : NeZero (g ^ d - 1) := ⟨(_root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos hd).ne'⟩
  obtain ⟨i, -, hi⟩ := (_root_.GlobalTheory.GoodCharsCompare.rootC_prim (g := g) hd).eq_pow_of_pow_eq_one
    (ξ := ω y) (by rw [← map_pow, hy, map_one])
  exact ⟨i, hi.symm⟩

theorem pow_eq_of_rootC {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ (g ^ d - 1) = 1) {a b : ℕ}
    (h : rootC (g ^ d - 1) ^ a = rootC (g ^ d - 1) ^ b) : z ^ a = z ^ b := by
  haveI : NeZero (g ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨m, -, rfl⟩ := (rootC_prim (g := g) hd).eq_pow_of_pow_eq_one hz
  rw [← pow_mul, mul_comm, pow_mul, h, ← pow_mul, ← pow_mul, mul_comm]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.labelChar_eq (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d)
    {x y : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) {m : ℕ}
    (hm : ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ m) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.labelChar ω d x y = ω x ^ m := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.labelChar
  have npos := _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos (g := g) hd
  have hprim := _root_.GlobalTheory.GoodCharsCompare.rootC_prim (g := g) hd
  have red : ∀ ξ : ℂ, ξ ^ (g ^ d - 1) = 1 → ∀ k, ξ ^ k = ξ ^ (k % (g ^ d - 1)) := by
    intro ξ hξ k
    conv_lhs => rw [← Nat.mod_add_div k (g ^ d - 1), pow_add, pow_mul, hξ, one_pow, mul_one]
  have hs : ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^
      sInf {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a} :=
    Nat.sInf_mem (s := {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a}) ⟨m, hm⟩
  have hxn : ω x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hmod : sInf {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a} % (g ^ d - 1) =
      m % (g ^ d - 1) := by
    apply hprim.pow_inj (Nat.mod_lt _ npos) (Nat.mod_lt _ npos)
    rw [← red _ hprim.pow_eq_one, ← red _ hprim.pow_eq_one]
    exact hs.symm.trans hm
  rw [red _ hxn, hmod, ← red _ hxn]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_preimage {ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ}
    (hω : Function.Injective ω) {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ (g ^ d - 1) = 1) :
    ∃ y : _root_.Formalism.CyclotomicNorms.Fbar g, y ^ (g ^ d - 1) = 1 ∧ ω y = z := by
  classical
  have hg : g.Prime := Fact.out
  have npos := _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos (g := g) hd
  have hnF : ((g ^ d - 1 : ℕ) : _root_.Formalism.CyclotomicNorms.Fbar g) ≠ 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow d g hg.pos), Nat.cast_pow, CharP.cast_eq_zero,
      zero_pow hd.ne', zero_sub, Nat.cast_one, neg_ne_zero]
    exact one_ne_zero
  have hsep : (X ^ (g ^ d - 1) - C (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).Separable :=
    separable_X_pow_sub_C 1 hnF one_ne_zero
  have hA : (nthRoots (g ^ d - 1) (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).toFinset.card = g ^ d - 1 := by
    unfold nthRoots
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      natDegree_X_pow_sub_C]
  have himage : (nthRoots (g ^ d - 1) (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).toFinset.image ω ⊆
      (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [Multiset.mem_toFinset, mem_nthRoots npos] at hy ⊢
    rw [← map_pow, hy, map_one]
  have hcardB : (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset.card ≤ g ^ d - 1 :=
    (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)
  have heq := Finset.eq_of_subset_of_card_le himage
    (by rw [Finset.card_image_of_injective _ hω, hA]; exact hcardB)
  have hzB : z ∈ (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset := by
    rw [Multiset.mem_toFinset, mem_nthRoots npos]
    exact hz
  rw [← heq] at hzB
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzB
  rw [Multiset.mem_toFinset, mem_nthRoots npos] at hy
  exact ⟨y, hy, rfl⟩

theorem exists_matrix {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι) {y : Fbar g}
    (hy : y ^ (g ^ Fintype.card ι - 1) = 1) :
    ∃ M : Matrix ι ι (ZMod g), minpoly (ZMod g) M = minpoly (ZMod g) y := by
  haveI : NeZero (g ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨φ, u, hu⟩ := exists_prim (g := g) hd
  obtain ⟨m, -, hm⟩ := hu.eq_pow_of_pow_eq_one hy
  let B : Module.Basis ι (ZMod g) (GaloisField g (Fintype.card ι)) :=
    (Module.finBasisOfFinrankEq _ _ (GaloisField.finrank g hd.ne')).reindex (Fintype.equivFin ι).symm
  refine ⟨Algebra.leftMulMatrix B (u ^ m), ?_⟩
  rw [minpoly.algHom_eq _ (Algebra.leftMulMatrix_injective B), ← hm, ← map_pow, minpoly.algHom_eq _ φ.injective]

theorem charpoly_eq_pow {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) {y : Fbar g}
    (h : minpoly (ZMod g) M = minpoly (ZMod g) y) : ∃ k, M.charpoly = minpoly (ZMod g) y ^ k := by
  have hm : aeval (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g))))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g))) = 0 := by
    have h1 := minpoly.aeval (ZMod g) M
    rw [h] at h1
    have h2 : aeval (M.map (algebraMap (ZMod g) (Fbar g))) (minpoly (ZMod g) y) = 0 := by
      have := aeval_algHom_apply (Algebra.ofId (ZMod g) (Fbar g)).mapMatrix M (minpoly (ZMod g) y)
      rw [h1, map_zero] at this
      exact this
    have h3 := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := Fbar g) (n := ι)) (M.map (algebraMap (ZMod g) (Fbar g)))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g)))
    rw [aeval_map_algebraMap (Fbar g) (M.map (algebraMap (ZMod g) (Fbar g))), h2, map_zero] at h3
    exact h3
  have key : ∀ q : (ZMod g)[X], q.Monic → Irreducible q → q ∣ M.charpoly → q = minpoly (ZMod g) y := by
    intro q hq hi hd
    obtain ⟨z, rfl⟩ := exists_minpoly hq hi
    have hz : aeval z M.charpoly = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval _ _)
    have hev : Module.End.HasEigenvalue (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map, IsRoot,
        eval_map_algebraMap]
      exact hz
    rw [Module.End.hasEigenvalue_iff_isRoot] at hev
    have h3 := hev.dvd (minpoly.dvd _ _ hm)
    rw [IsRoot, eval_map_algebraMap] at h3
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (isInt y)) h3 (minpoly.monic (isInt y))).symm
  have gen : ∀ n, ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → f ∣ M.charpoly →
      ∃ k, f = minpoly (ZMod g) y ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn hd
      by_cases h1 : f = 1
      · exact ⟨0, by simp [h1]⟩
      · have hu : ¬ IsUnit f := fun hu => h1 (hf.isUnit_iff.1 hu)
        obtain ⟨P, hPm, hP, t, rfl⟩ := exists_monic_irreducible_factor f hu
        have hh : t.Monic := hPm.of_mul_monic_left hf
        have hlt : t.natDegree < n := by
          rw [← hn, hPm.natDegree_mul hh]
          have := hP.natDegree_pos
          omega
        obtain ⟨k, hk⟩ := ih _ hlt t hh rfl (dvd_of_mul_left_dvd hd)
        exact ⟨k + 1, by rw [pow_succ', ← hk, ← key P hPm hP (dvd_of_mul_right_dvd hd)]⟩
  exact gen _ _ M.charpoly_monic rfl dvd_rfl

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.rootsBar_pow (f : (ZMod g)[X]) (k : ℕ) : _root_.Formalism.CyclotomicNorms.rootsBar (f ^ k) = k • _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, roots_pow]

theorem finrank_eig {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) {y : Fbar g}
    (h : minpoly (ZMod g) M = minpoly (ZMod g) y) {k : ℕ} (hk : M.charpoly = minpoly (ZMod g) y ^ k)
    {z : Fbar g} (hz : z ∈ rootsBar (minpoly (ZMod g) y)) :
    Module.finrank (Fbar g) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z) = k := by
  classical
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hm : aeval (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g))))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g))) = 0 := by
    have h1 := minpoly.aeval (ZMod g) M
    rw [h] at h1
    have h2 : aeval (M.map (algebraMap (ZMod g) (Fbar g))) (minpoly (ZMod g) y) = 0 := by
      have := aeval_algHom_apply (Algebra.ofId (ZMod g) (Fbar g)).mapMatrix M (minpoly (ZMod g) y)
      rw [h1, map_zero] at this
      exact this
    have h3 := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := Fbar g) (n := ι)) (M.map (algebraMap (ZMod g) (Fbar g)))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g)))
    rw [aeval_map_algebraMap (Fbar g) (M.map (algebraMap (ZMod g) (Fbar g))), h2, map_zero] at h3
    exact h3
  have hss := Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (PerfectField.separable_of_irreducible (minpoly.irreducible (isInt y))).map.squarefree hm
  rw [← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, LinearMap.finrank_maxGenEigenspace_eq,
    Matrix.charpoly_toLin', Matrix.charpoly_map, ← count_roots]
  change Multiset.count z (rootsBar M.charpoly) = k
  rw [hk, rootsBar_pow, Multiset.count_nsmul, Multiset.count_eq_one_of_mem (nodup_minpoly y) hz, mul_one]

theorem cuspVal_eq_torusValue (ω : Fbar g →*₀ ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι)
    (M : Matrix ι ι (ZMod g)) {x y : Fbar g} (hx : x ^ (g ^ Fintype.card ι - 1) = 1)
    (h : minpoly (ZMod g) M = minpoly (ZMod g) y) {m : ℕ} (hm : ω y = rootC (g ^ Fintype.card ι - 1) ^ m) :
    cuspVal ω x M = torusValue g (Fintype.card ι) (dg y) (ω x) m := by
  classical
  obtain ⟨k, hk⟩ := charpoly_eq_pow M h
  have hdk : Fintype.card ι = dg y * k := by
    rw [← M.charpoly_natDegree_eq_dim, hk, (minpoly.monic (isInt y)).natDegree_pow, mul_comm]
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left (hdk ▸ hd)
  have hq : Fintype.card ι / dg y = k := by rw [hdk, Nat.mul_div_cancel_left _ (dg_pos y)]
  have hR : (rootsBar M.charpoly).toFinset = (rootsBar (minpoly (ZMod g) y)).toFinset := by
    rw [hk, rootsBar_pow, Multiset.toFinset_nsmul _ _ hk0.ne']
  have hcard : (rootsBar (minpoly (ZMod g) y)).toFinset.card = dg y := by
    rw [Multiset.toFinset_card_of_nodup (nodup_minpoly y), card_rootsBar]
  rw [cuspVal, if_pos ⟨_, k, minpoly.irreducible (isInt y), hk⟩, torusValue, hq]
  have e1 : ∀ z ∈ (rootsBar (minpoly (ZMod g) y)).toFinset,
      labelChar ω (Fintype.card ι) x z * ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z)),
          (1 - (g : ℂ) ^ (dg y * i)) =
      labelChar ω (Fintype.card ι) x z * ∏ i ∈ Finset.Ico 1 k, (1 - (g : ℂ) ^ (dg y * i)) := by
    intro z hz
    rw [finrank_eig M h hk (Multiset.mem_toFinset.1 hz)]
  have e2 : ∑ z ∈ (rootsBar (minpoly (ZMod g) y)).toFinset, labelChar ω (Fintype.card ι) x z =
      ∑ i ∈ Finset.range (dg y), ω x ^ (m * g ^ i) := by
    rw [roots_minpoly, Finset.sum_image]
    · refine Finset.sum_congr rfl fun i _ => labelChar_eq ω hd hx ?_
      rw [map_pow, hm, ← pow_mul]
    · intro i hi j hj h
      exact (frobenius_orbit_degreeOverPrimeFieldFbar y).2 i (by simpa using hi) j (by simpa using hj) h
  have e3 : ∏ i ∈ Finset.Ico 1 k, (1 - (g : ℂ) ^ (dg y * i)) =
      (-1) ^ (k - 1) * ∏ i ∈ Finset.Ico 1 k, ((g : ℂ) ^ (dg y * i) - 1) := by
    rw [← Nat.card_Ico, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  have e4 : (-1 : ℂ) ^ (Fintype.card ι - 1) * (-1) ^ (k - 1) = (-1) ^ (Fintype.card ι - k) := by
    have hle : k ≤ Fintype.card ι := hdk ▸ Nat.le_mul_of_pos_left _ (dg_pos y)
    rw [← pow_add, show Fintype.card ι - 1 + (k - 1) = Fintype.card ι - k + 2 * (k - 1) by omega, pow_add, pow_mul]
    simp
  have e5 := Finset.sum_congr rfl e1
  rw [← Finset.sum_mul, e2, e3] at e5
  have := hR
  convert_to (-1) ^ (Fintype.card ι - 1) * (∑ z ∈ (rootsBar (minpoly (ZMod g) y)).toFinset,
      labelChar ω (Fintype.card ι) x z * ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z)),
          (1 - (g : ℂ) ^ (dg y * i))) = _
  · rw [← hcard, ← hR]
  rw [e5, ← e4]
  ring

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.sum_shift {z : ℂ} {m e : ℕ} (h : z ^ (m * g ^ e) = z ^ m) (j : ℕ) :
    ∑ i ∈ Finset.range e, (z ^ g ^ j) ^ (m * g ^ i) = ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
  have hper : ∀ i, z ^ (m * g ^ (i + e)) = z ^ (m * g ^ i) := fun i => by
    rw [show m * g ^ (i + e) = m * g ^ e * g ^ i by ring, pow_mul, h, ← pow_mul]
  have shift : ∀ j, ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) =
      ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (e + 1), z ^ (m * g ^ (i + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + 1 + j)) + z ^ (m * g ^ (0 + j)) :=
        Finset.sum_range_succ' _ _
      have h2 : ∑ i ∈ Finset.range (e + 1), z ^ (m * g ^ (i + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) + z ^ (m * g ^ (e + j)) :=
        Finset.sum_range_succ _ _
      have h3 : z ^ (m * g ^ (e + j)) = z ^ (m * g ^ (0 + j)) := by
        rw [add_comm e j, hper, zero_add]
      have h4 : ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + 1 + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) :=
        add_right_cancel (h1.symm.trans (h2.trans (congrArg (HAdd.hAdd _) h3)))
      rw [← ih, ← h4]
      exact Finset.sum_congr rfl fun i _ => by rw [show i + (j + 1) = i + 1 + j by omega]
  rw [← shift j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul]
  congr 1
  ring

theorem sum_period {z : ℂ} {m e : ℕ} (h : z ^ (m * g ^ e) = z ^ m) (k : ℕ) :
    ∑ i ∈ Finset.range (e * k), z ^ (m * g ^ i) = k * ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul, ← sum_shift h (e * k)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
    congr 1
    ring

theorem period_of (ω : Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d) {x y : Fbar g} (hx : x ^ (g ^ d - 1) = 1) {m : ℕ}
    (hm : ω y = rootC (g ^ d - 1) ^ m) : ω x ^ (m * g ^ dg y) = ω x ^ m := by
  refine pow_eq_of_rootC (g := g) hd (by rw [← map_pow, hx, map_one]) ?_
  rw [pow_mul, ← hm, ← map_pow, (frobenius_orbit_degreeOverPrimeFieldFbar y).1]

theorem mem_orbit_of_sums {z w : ℂ} {d : ℕ} (hd : 0 < d)
    (h : ∀ m : ℕ, ∑ i ∈ Finset.range d, z ^ (m * g ^ i) = ∑ i ∈ Finset.range d, w ^ (m * g ^ i)) :
    ∃ j, w = z ^ g ^ j := by
  classical
  by_contra hn
  push Not at hn
  have hQ : ∀ Q : ℂ[X], ∑ i ∈ Finset.range d, Q.eval (z ^ g ^ i) = ∑ i ∈ Finset.range d, Q.eval (w ^ g ^ i) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simp only [eval_add, Finset.sum_add_distrib, hp, hq]
    | monomial n a =>
      simp only [eval_monomial, ← Finset.mul_sum, ← pow_mul]
      have := h n
      simp only [mul_comm n] at this
      rw [this]
  let S : Finset ℂ := (((Finset.range d).image fun i => z ^ g ^ i) ∪ (Finset.range d).image fun i => w ^ g ^ i).erase w
  let Q : ℂ[X] := ∏ a ∈ S, (X - C a)
  have hz : ∀ a ∈ S, Q.eval a = 0 := by
    intro a ha
    rw [eval_prod]
    exact Finset.prod_eq_zero ha (by simp)
  have hw : Q.eval w ≠ 0 := by
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun a ha => ?_
    simpa [sub_eq_zero] using (Finset.ne_of_mem_erase ha).symm
  have h1 := hQ Q
  rw [Finset.sum_eq_zero (fun i hi => hz _ (Finset.mem_erase.2 ⟨(hn i).symm,
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)⟩))] at h1
  have h2 : ∑ i ∈ Finset.range d, Q.eval (w ^ g ^ i) =
      ∑ i ∈ (Finset.range d).filter (fun i => w ^ g ^ i = w), Q.eval w := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    split_ifs with hh
    · rw [hh]
    · exact hz _ (Finset.mem_erase.2 ⟨hh, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)⟩)
  rw [h2, Finset.sum_const, nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1.symm with h3 | h3
  · have : 0 ∈ (Finset.range d).filter (fun i => w ^ g ^ i = w) := by simp [hd]
    exact Finset.card_ne_zero_of_mem this (by exact_mod_cast h3)
  · exact hw h3

end GlobalTheory.GoodCharsCompare
