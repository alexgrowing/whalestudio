import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitDegreeOverPrimeFieldFbar
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField

noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_dg_mul_eq_self (y : _root_.Formalism.CyclotomicNorms.Fbar g) (q : ℕ) :
    y ^ g ^ (_root_.GlobalTheory.GoodCharsCompare.dg y * q) = y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_dg_mul {d : ℕ} (hd : 0 < d) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ^ (g ^ d - 1) = 1) : ∃ k, d = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
  have hDpos := _root_.GlobalTheory.GoodCharsCompare.dg_pos y
  have hd' : y ^ g ^ d = y := _root_.GlobalTheory.GoodCharsCompare.pow_g_of hy
  refine ⟨d / _root_.GlobalTheory.GoodCharsCompare.dg y, ?_⟩
  have hr : y ^ g ^ (d % _root_.GlobalTheory.GoodCharsCompare.dg y) = y ^ g ^ 0 := by
    rw [pow_zero, pow_one]
    conv_rhs => rw [← hd', ← Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y), pow_add, pow_mul,
      pow_pow_dg_mul_eq_self]
  have h1 := (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 _ (Nat.mod_lt _ hDpos) 0 hDpos hr
  have h2 := Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y)
  rw [h1, add_zero] at h2
  exact h2.symm

theorem exists_unit_of_pow {y : Fbar g} (hy : y ^ (g ^ 1 - 1) = 1) :
    ∃ c : (ZMod g)ˣ, algebraMap (ZMod g) (Fbar g) c = y := by
  obtain ⟨k, hk⟩ := exists_dg_mul one_pos hy
  have h1 : dg y = 1 := Nat.eq_one_of_mul_eq_one_right hk.symm
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, zero_pow (g_pow_sub_pos one_pos).ne'] at hy
    exact zero_ne_one hy
  exact ⟨Units.mk0 c hc0, hc⟩

theorem unit_pow (c : (ZMod g)ˣ) : algebraMap (ZMod g) (Fbar g) c ^ (g ^ 1 - 1) = 1 := by
  rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one]

theorem exists_alpha {ω ω' : Fbar g →*₀ ℂ} (hω : Function.Injective ω) (hω' : Function.Injective ω') :
    ∃ α : Fbar g ≃* Fbar g, ∀ x, ω (α x) = ω' x := by
  have key : ∀ {ω ω' : Fbar g →*₀ ℂ}, Function.Injective ω → ∀ x, ∃ z, ω z = ω' x := by
    intro ω ω' hω x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · obtain ⟨z, -, hz⟩ := exists_preimage hω (dg_pos x) (z := ω' x) (by rw [← map_pow, pow_dg hx, map_one])
      exact ⟨z, hz⟩
  choose a ha using key (ω' := ω') hω
  choose a' ha' using key (ω' := ω) hω'
  exact ⟨⟨⟨a, a', fun x => hω' (by rw [ha', ha]), fun x => hω (by rw [ha, ha'])⟩,
    fun x y => hω (by simp only [ha, map_mul])⟩, ha⟩

theorem exists_exp (α : Fbar g ≃* Fbar g) {d : ℕ} (hd : 0 < d) :
    ∃ a : ℕ, ∀ z : Fbar g, z ^ (g ^ d - 1) = 1 → α z = z ^ a := by
  have : NeZero (g ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨φ, u, hu⟩ := exists_prim (g := g) hd
  obtain ⟨a, -, ha⟩ := hu.eq_pow_of_pow_eq_one (ξ := α (φ u)) (by rw [← map_pow, hu.pow_eq_one, map_one])
  refine ⟨a, fun z hz => ?_⟩
  obtain ⟨k, -, rfl⟩ := hu.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_beta {ω ω' : Fbar g →*₀ ℂ} (hω : Function.Injective ω) (hω' : Function.Injective ω') :
    ∃ β : Fbar g ≃* Fbar g, ∀ d, 0 < d → ∀ x y : Fbar g, x ^ (g ^ d - 1) = 1 → y ^ (g ^ d - 1) = 1 →
      labelChar ω' d x y = labelChar ω d (β x) y := by
  obtain ⟨α, hα⟩ := exists_alpha hω hω'
  refine ⟨α.trans α, fun d hd x y hx hy => ?_⟩
  obtain ⟨a, ha⟩ := exists_exp α hd
  obtain ⟨n, hn⟩ := exists_log ω hd hy
  have hx1 : α x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hx2 : α (α x) ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx1, map_one]
  rw [labelChar_eq ω' hd hx (m := n * a) (by rw [← hα, ha y hy, map_pow, hn, ← pow_mul]), MulEquiv.trans_apply,
    labelChar_eq ω hd hx2 hn, ha _ hx1, map_pow, hα, ← pow_mul, mul_comm]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_sub_one_eq_one_of_pow_pow_eq_self {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.root_pow {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι (ZMod g)} (hM : M.det ≠ 0)
    {p : (ZMod g)[X]} {k : ℕ} (hp : Irreducible p) (hk : M.charpoly = p ^ k) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ∈ _root_.Formalism.CyclotomicNorms.rootsBar M.charpoly) : y ^ (g ^ Fintype.card ι - 1) = 1 := by
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  have hchar0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, ← coeff_zero_eq_aeval_zero',
      map_eq_zero] at hy
    apply hM
    rw [Matrix.det_eq_sign_charpoly_coeff, hy, mul_zero]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [hk, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar one_ne_zero, map_one] at hy
    exact one_ne_zero hy
  have hyp : aeval y p = 0 := by
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, hk, map_pow] at hy
    exact (pow_eq_zero_iff hk0).mp hy
  have hdvd : minpoly (ZMod g) y ∣ p := minpoly.dvd _ _ hyp
  have hassoc : Associated (minpoly (ZMod g) y) p :=
    associated_of_dvd_dvd hdvd ((minpoly.irreducible hint).dvd_symm hp hdvd)
  have hdeg : p.natDegree = _root_.GlobalTheory.GoodCharsCompare.dg y :=
    (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)).symm
  have hcard : Fintype.card ι = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hk, natDegree_pow, hdeg, mul_comm]
  apply pow_pow_sub_one_eq_one_of_pow_pow_eq_self hy0
  rw [hcard]
  exact pow_pow_dg_mul_eq_self y k

theorem cuspVal_congr {ω ω' : Fbar g →*₀ ℂ} {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι (ZMod g)}
    (hM : M.det ≠ 0) {x x' : Fbar g} (h : ∀ y : Fbar g, y ^ (g ^ Fintype.card ι - 1) = 1 →
      labelChar ω' (Fintype.card ι) x y = labelChar ω (Fintype.card ι) x' y) : cuspVal ω' x M = cuspVal ω x' M := by
  unfold cuspVal
  split_ifs with hh
  · obtain ⟨p, k, hp, hk⟩ := hh
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [h y (root_pow hM hp hk (by simpa using hy))]
  · rfl

def Tr (β : Fbar g ≃* Fbar g) (f f' : (ZMod g)[X]) : Prop :=
  f'.Monic ∧ rootsBar f' = (rootsBar f).map β

theorem Tr.mul {β : Fbar g ≃* Fbar g} {f f' h h' : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0)
    (h1 : Tr β f f') (h2 : Tr β h h') : Tr β (f * h) (f' * h') :=
  ⟨h1.1.mul h2.1, by
    rw [rootsBar_mul h1.1.ne_zero h2.1.ne_zero, rootsBar_mul hf hh, h1.2, h2.2, Multiset.map_add]⟩

theorem Tr.unique {β : Fbar g ≃* Fbar g} {f f' f'' : (ZMod g)[X]} (h1 : Tr β f f') (h2 : Tr β f f'') : f' = f'' :=
  eq_of_rootsBar h1.1 h2.1 (h1.2.trans h2.2.symm)

theorem Tr.symm {β : Fbar g ≃* Fbar g} {f f' : (ZMod g)[X]} (hf : f.Monic) (h1 : Tr β f f') : Tr β.symm f' f :=
  ⟨hf, by rw [h1.2, Multiset.map_map]; simp⟩

theorem Tr.natDegree {β : Fbar g ≃* Fbar g} {f f' : (ZMod g)[X]} (h1 : Tr β f f') : f'.natDegree = f.natDegree := by
  rw [← card_rootsBar, h1.2, Multiset.card_map, card_rootsBar]

theorem tr_minpoly (β : Fbar g ≃* Fbar g) (x : Fbar g) : Tr β (minpoly (ZMod g) x) (minpoly (ZMod g) (β x)) := by
  refine ⟨minpoly.monic (isInt _), ?_⟩
  rw [Multiset.Nodup.ext (nodup_minpoly _) ((nodup_minpoly x).map β.injective)]
  intro y
  rw [mem_roots_minpoly, Multiset.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨x ^ g ^ i, mem_roots_minpoly.2 ⟨i, rfl⟩, map_pow _ _ _⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨i, rfl⟩ := mem_roots_minpoly.1 hz
    exact ⟨i, map_pow _ _ _⟩

theorem tr_one (β : Fbar g ≃* Fbar g) : Tr β 1 1 := ⟨monic_one, by simp [rootsBar]⟩

theorem tr_prod (β : Fbar g ≃* Fbar g) (s : Finset ℕ) (φ φ' : ℕ → (ZMod g)[X]) (h0 : ∀ c ∈ s, (φ c).Monic)
    (h : ∀ c ∈ s, Tr β (φ c) (φ' c)) : Tr β (∏ c ∈ s, φ c) (∏ c ∈ s, φ' c) := by
  induction s using Finset.induction_on with
  | empty => simpa using tr_one β
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Tr.mul (h0 a (by simp)).ne_zero (monic_prod_of_monic _ _ fun c hc => h0 c (by simp [hc])).ne_zero
      (h a (by simp)) (ih (fun c hc => h0 c (by simp [hc])) fun c hc => h c (by simp [hc]))

theorem exists_tr (β : Fbar g ≃* Fbar g) (n : ℕ) :
    ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → ∃ f', Tr β f f' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn
    by_cases h1 : f = 1
    · exact ⟨1, h1 ▸ tr_one β⟩
    · have hu : ¬ IsUnit f := fun hu => h1 (hf.isUnit_iff.1 hu)
      obtain ⟨P, hPm, hP, h, rfl⟩ := exists_monic_irreducible_factor f hu
      have hh : h.Monic := hPm.of_mul_monic_left hf
      have hd : h.natDegree < n := by
        rw [← hn, hPm.natDegree_mul hh]
        have := hP.natDegree_pos
        omega
      obtain ⟨h', hh'⟩ := ih _ hd h hh rfl
      obtain ⟨x, rfl⟩ := exists_minpoly hPm hP
      exact ⟨_, (tr_minpoly β x).mul hPm.ne_zero hh.ne_zero hh'⟩

theorem Tr.dvd {β : Fbar g ≃* Fbar g} {f f' q q' : (ZMod g)[X]} (hf : f.Monic) (hq : q.Monic) (h : Tr β f f')
    (h' : Tr β q q') (hd : q ∣ f) : q' ∣ f' := by
  obtain ⟨t, rfl⟩ := hd
  have ht := hq.of_mul_monic_left hf
  obtain ⟨t', ht'⟩ := exists_tr β _ t ht rfl
  exact ⟨t', h.unique (h'.mul hq.ne_zero ht.ne_zero ht')⟩

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.coeff_zero_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    f.coeff 0 ≠ 0 ↔ (0 : _root_.Formalism.CyclotomicNorms.Fbar g) ∉ _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, ← aeval_def,
    ← coeff_zero_eq_aeval_zero', map_eq_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.squarefree_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    Squarefree f ↔ (_root_.Formalism.CyclotomicNorms.rootsBar f).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (IsAlgClosed.splits _), separable_map,
    PerfectField.separable_iff_squarefree]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.primeToPart_map (β : _root_.Formalism.CyclotomicNorms.Fbar g ≃* _root_.Formalism.CyclotomicNorms.Fbar g) (l : ℕ) (x : _root_.Formalism.CyclotomicNorms.Fbar g) :
    _root_.Formalism.CyclotomicNorms.primeToPart l (β x) = β (_root_.Formalism.CyclotomicNorms.primeToPart l x) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [MulEquiv.orderOf_eq, map_pow]

theorem isGood_tr {N : ℕ} {P J : Type} (β : P → Fbar g ≃* Fbar g) {f f' : P → (ZMod g)[X]} {χ χ' : P → J → (ZMod g)ˣ}
    (h : ∀ v, Tr (β v) (f v) (f' v))
    (hχ : ∀ v j, algebraMap (ZMod g) (Fbar g) (χ' v j) = β v (algebraMap (ZMod g) (Fbar g) (χ v j)))
    (H : IsGood N g f χ) : IsGood N g f' χ' := by
  obtain ⟨h1, h2, h3, h4, h5, v, q, hq, hqd, h6⟩ := H
  refine ⟨fun v => ⟨(h v).1, (h v).natDegree.trans (h1 v).2.1, ?_⟩, fun v => ?_, ?_, ?_, ?_, ?_⟩
  · rw [coeff_zero_iff (h v).1.ne_zero, (h v).2, Multiset.mem_map]
    rintro ⟨z, hz, h0⟩
    rw [map_eq_zero] at h0
    exact (coeff_zero_iff (h1 v).1.ne_zero).1 (h1 v).2.2 (h0 ▸ hz)
  · rw [squarefree_iff (h v).1.ne_zero, (h v).2]
    exact ((squarefree_iff (h1 v).1.ne_zero).1 (h2 v)).map (β v).injective
  · intro l hl hb v x hx y hy hxy
    rw [(h v).2, Multiset.mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [primeToPart_map, primeToPart_map] at hxy
    rw [h3 l hl hb v x hx y hy ((β v).injective hxy)]
  · intro l hl hb v j x hx hxy
    rw [(h v).2, Multiset.mem_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    rw [hχ, primeToPart_map, primeToPart_map] at hxy
    exact h4 l hl hb v j x hx ((β v).injective hxy)
  · intro a ha hb
    obtain ⟨v, hv⟩ := h5 a ha hb
    refine ⟨v, ?_⟩
    rintro ⟨q, hq, rfl⟩
    have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero (h v).1.ne_zero hq
    have hm := monic_normalize hq0
    obtain ⟨q', hq'⟩ := exists_tr (β v).symm _ _ hm rfl
    refine hv ⟨q', Tr.dvd (h v).1 hm ((h v).symm (h1 v).1) hq' (normalize_dvd_iff.2 hq), ?_⟩
    rw [hq'.natDegree]
    exact natDegree_eq_of_degree_eq (degree_normalize)
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) q (degree_pos_of_irreducible hq).ne'
    have e1 := minpoly.eq_of_irreducible hq hx
    have e2 : (minpoly (ZMod g) (β v x)).natDegree = q.natDegree := by
      rw [(tr_minpoly (β v) x).natDegree, ← e1, natDegree_mul_leadingCoeff_inv _ hq.ne_zero]
    refine ⟨v, minpoly (ZMod g) (β v x), minpoly.irreducible (isInt _),
      Tr.dvd (h1 v).1 (minpoly.monic (isInt x)) (h v) (tr_minpoly _ x) ((minpoly.dvd _ _ hx).trans hqd), ?_⟩
    rw [e2]
    exact h6

theorem blkSize_eq {r : ℕ} (b : Fin r → ℕ) (c : ℕ) : blkSize b c = Fintype.card {a : Fin r // b a = c} :=
  (Fintype.card_subtype _).symm

theorem card_blk_pos {r : ℕ} {b : Fin r → ℕ} {c : ℕ} (hc : c ∈ Finset.univ.image b) :
    0 < Fintype.card {a : Fin r // b a = c} := by
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hc
  exact Fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩

theorem det_blkMat_ne {r : ℕ} (b : Fin r → ℕ) (c : ℕ) (p : blockTri (κ := ZMod g) b) : (blkMat b c p).det ≠ 0 :=
  (blkDet b c p).ne_zero

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_minpoly {φ : (ZMod g)[X]} (hm : φ.Monic)
    (hi : Irreducible φ) {x : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ _root_.Formalism.CyclotomicNorms.rootsBar φ) : φ = minpoly (ZMod g) x :=
  minpoly.eq_of_irreducible_of_monic hi
    ((_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hm.ne_zero).mp hx) hm

theorem root_ne_zero {s : Finset ℕ} {φ : ℕ → (ZMod g)[X]} (h0 : (∏ c ∈ s, φ c).coeff 0 ≠ 0) {c : ℕ} (hc : c ∈ s)
    (hm : (φ c).Monic) {x : Fbar g} (hx : x ∈ rootsBar (φ c)) : x ≠ 0 := by
  rintro rfl
  rw [coeff_zero_prod] at h0
  exact (coeff_zero_iff hm.ne_zero).1 (Finset.prod_ne_zero_iff.1 h0 c hc) hx

theorem isTypeChar_tr {ω ω' : Fbar g →*₀ ℂ} {β : Fbar g ≃* Fbar g}
    (hβ : ∀ d, 0 < d → ∀ x y : Fbar g, x ^ (g ^ d - 1) = 1 → y ^ (g ^ d - 1) = 1 →
      labelChar ω' d x y = labelChar ω d (β x) y) {r : ℕ} {f f' : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) (hf : Tr β f f')
    {ch : GL (Fin r) (ZMod g) → ℂ} (h : IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar ω' f ch) : IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar ω f' ch := by
  obtain ⟨b, φ, x, n, ρ, h1, rfl, h3, h4, h5⟩ := h
  have e : ∀ c ∈ Finset.univ.image b, φ c = minpoly (ZMod g) (x c) := fun c hc =>
    eq_minpoly (h1 c hc).1 (h1 c hc).2.1 (h1 c hc).2.2.2
  refine ⟨b, fun c => minpoly (ZMod g) (β (x c)), fun c => β (x c), n, ρ, fun c hc => ⟨minpoly.monic (isInt _),
    minpoly.irreducible (isInt _), ?_, mem_roots_minpoly.2 ⟨0, by simp⟩⟩, ?_, h3, fun p => ?_, h5⟩
  · rw [(tr_minpoly β (x c)).natDegree, ← e c hc, (h1 c hc).2.2.1]
  · exact hf.unique (tr_prod β _ _ _ (fun c hc => (h1 c hc).1) fun c hc => e c hc ▸ tr_minpoly β (x c))
  · rw [h4]
    refine Finset.prod_congr rfl fun c hc => cuspVal_congr (det_blkMat_ne b c p) fun y hy =>
      hβ _ (card_blk_pos hc) _ _ ?_ hy
    rw [← (h1 c hc).2.2.1, e c hc]
    exact pow_dg (root_ne_zero h0 hc (h1 c hc).1 (h1 c hc).2.2.2)

def Ext (ι : (Fbar g)ˣ →* ℂˣ) (ω : Fbar g →*₀ ℂ) : Prop := ∀ u : (Fbar g)ˣ, ((ι u : ℂˣ) : ℂ) = ω u

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_ext {ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ}
    (hι : Function.Injective ι) :
    ∃ ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ, Function.Injective ω ∧ _root_.GlobalTheory.GoodCharsCompare.Ext ι ω := by
  classical
  let f : _root_.Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if h : x = 0 then 0 else ((ι (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((ι (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  refine ⟨ω, ?_, ?_⟩
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have := hι (Units.ext hab)
      simpa using congrArg Units.val this
  · intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]

theorem label_iff {ι : (Fbar g)ˣ →* ℂˣ} {ω : Fbar g →*₀ ℂ} (he : Ext ι ω) (θ : (ZMod g)ˣ → ℂ) (a : (ZMod g)ˣ) :
    IsCharLabel ι θ a ↔ IsTameLabel ω θ a := by
  unfold IsCharLabel IsTameLabel
  simp only [he _, rootOfOne_eq, Units.coe_map, MonoidHom.coe_coe]
  constructor
  · intro h z
    obtain ⟨m, hm⟩ := exists_log ω one_pos (unit_pow z)
    rw [h z m hm, labelChar_eq ω one_pos (unit_pow a) hm]
  · intro h z m hm
    rw [h z, labelChar_eq ω one_pos (unit_pow a) hm]

theorem label_unique {ω : Fbar g →*₀ ℂ} (hω : Function.Injective ω) {θ : (ZMod g)ˣ → ℂ} {a a' : (ZMod g)ˣ}
    (h : IsTameLabel ω θ a) (h' : IsTameLabel ω θ a') : a = a' := by
  obtain ⟨y, hy, hy'⟩ := exists_preimage hω one_pos (rootC_prim (g := g) one_pos).pow_eq_one
  obtain ⟨z, rfl⟩ := exists_unit_of_pow hy
  have e := (h z).symm.trans (h' z)
  rw [← pow_one (rootC _)] at hy'
  rw [labelChar_eq ω one_pos (unit_pow a) hy', labelChar_eq ω one_pos (unit_pow a') hy', pow_one, pow_one] at e
  exact Units.ext ((algebraMap (ZMod g) (Fbar g)).injective (hω e))

theorem label_inv {ω : Fbar g →*₀ ℂ} {θ : (ZMod g)ˣ → ℂ} {a : (ZMod g)ˣ}
    (h : IsTameLabel ω θ a) : IsTameLabel ω (fun z => (θ z)⁻¹) a⁻¹ := by
  intro z
  obtain ⟨m, hm⟩ := exists_log ω one_pos (unit_pow z)
  show (θ z)⁻¹ = _
  rw [h z, labelChar_eq ω one_pos (unit_pow a) hm, labelChar_eq ω one_pos (unit_pow a⁻¹) hm,
    Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, inv_pow]

theorem exists_block {r : ℕ} (b : Fin r → ℕ) (y : ℕ → Fbar g)
    (hy : ∀ c ∈ Finset.univ.image b, y c ^ (g ^ Fintype.card {a : Fin r // b a = c} - 1) = 1) :
    ∃ p : blockTri (κ := ZMod g) b, ∀ c ∈ Finset.univ.image b,
      minpoly (ZMod g) (blkMat b c p) = minpoly (ZMod g) (y c) := by
  have h1 : ∀ c, ∃ M : Matrix {a : Fin r // b a = c} {a : Fin r // b a = c} (ZMod g),
      c ∈ Finset.univ.image b → minpoly (ZMod g) M = minpoly (ZMod g) (y c) := by
    intro c
    by_cases hc : c ∈ Finset.univ.image b
    · obtain ⟨M, hM⟩ := exists_matrix (card_blk_pos hc) (hy c hc)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose M hM using h1
  let A : Matrix (Fin r) (Fin r) (ZMod g) := fun i j => if h : b j = b i then M (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0
  have hA : A.BlockTriangular b := fun i j h => dif_neg (ne_of_lt h)
  have hB : ∀ c, A.toSquareBlock b c = M c := by
    intro c
    ext ⟨i, rfl⟩ ⟨j, hj⟩
    exact dif_pos hj
  have hdet : A.det ≠ 0 := by
    rw [hA.det]
    refine Finset.prod_ne_zero_iff.2 fun c hc => ?_
    obtain ⟨k, hk⟩ := charpoly_eq_pow _ (hM c hc)
    have hy0 : y c ≠ 0 := by
      intro h
      have := hy c hc
      rw [h, zero_pow (g_pow_sub_pos (card_blk_pos hc)).ne'] at this
      exact zero_ne_one this
    rw [hB, Matrix.det_eq_sign_charpoly_coeff, hk, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ (minpoly.coeff_zero_ne_zero (isInt _) hy0))
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, hA⟩, fun c hc => ?_⟩
  rw [← hM c hc, ← hB]
  rfl

theorem torus_coef_ne {d e : ℕ} (he : 0 < e) :
    ((-1 : ℂ) ^ (d - d / e) * ∏ i ∈ Finset.Ico 1 (d / e), ((g : ℂ) ^ (e * i) - 1)) ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (by simp)) (Finset.prod_ne_zero_iff.2 fun i hi => ?_)
  have h1 : 1 < g ^ (e * i) := Nat.one_lt_pow (Nat.mul_pos he (Finset.mem_Ico.1 hi).1).ne' (Fact.out : g.Prime).one_lt
  rw [sub_ne_zero]
  exact_mod_cast h1.ne'

def CuspidalCharacterFormula : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (ω : Fbar g →*₀ ℂ), Function.Injective ω → ∀ (r : ℕ) (b : Fin r → ℕ) (n : ℕ)
    (σ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)), IsCuspDatum b σ →
    ∃ x : ℕ → Fbar g, (∀ c ∈ Finset.univ.image b, x c ≠ 0 ∧
        (minpoly (ZMod g) (x c)).natDegree = Fintype.card {a : Fin r // b a = c}) ∧
      ∀ p, σ.character p = ∏ c ∈ Finset.univ.image b, cuspVal ω (x c) (blkMat b c p)

theorem typeChar_full_of_torus (H : CuspidalCharacterFormula) {ι : (Fbar g)ˣ →* ℂˣ} {ω : Fbar g →*₀ ℂ}
    (hω : Function.Injective ω) (he : Ext ι ω) {r : ℕ} {f : (ZMod g)[X]} {ch : GL (Fin r) (ZMod g) → ℂ}
    (h : IndefiniteRowSideFullHecke.TameCharacterTorusValues.IsTypeChar ι f ch) : IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar ω f ch := by
  classical
  obtain ⟨b, φ, n, σ, hL, rfl, h5⟩ := h
  obtain ⟨x₀, hx₀, hch⟩ := H g ω hω r b n σ hL.cusp
  refine ⟨b, φ, x₀, n, σ, fun c₀ hc₀ => ⟨hL.monic _ hc₀, hL.irred _ hc₀, by rw [hL.degree _ hc₀, blkSize_eq], ?_⟩,
    rfl, hL.cusp, hch, h5⟩
  have h1 : ∀ c, ∃ x : (Fbar g)ˣ, c ∈ Finset.univ.image b → φ c = minpoly (ZMod g) (x : Fbar g) := by
    intro c
    by_cases hc : c ∈ Finset.univ.image b
    · obtain ⟨x, hx⟩ := exists_minpoly (hL.monic c hc) (hL.irred c hc)
      have : x ≠ 0 := by
        rintro rfl
        exact hL.ne_X c hc (by rw [hx, minpoly.zero])
      exact ⟨Units.mk0 x this, fun _ => hx⟩
    · exact ⟨1, fun h => absurd h hc⟩
  choose x hx using h1
  have hxp : ∀ c ∈ Finset.univ.image b, (x c : Fbar g) ^ (g ^ Fintype.card {a : Fin r // b a = c} - 1) = 1 := by
    intro c hc
    rw [← blkSize_eq, ← hL.degree c hc, hx c hc]
    exact pow_dg (x c).ne_zero
  have hx₀p : ∀ c ∈ Finset.univ.image b, x₀ c ^ (g ^ Fintype.card {a : Fin r // b a = c} - 1) = 1 := by
    intro c hc
    rw [← (hx₀ c hc).2]
    exact pow_dg (hx₀ c hc).1
  have hd := card_blk_pos hc₀
  obtain ⟨j, hj⟩ := mem_orbit_of_sums (g := g) (z := ω (x c₀)) (w := ω (x₀ c₀)) hd (by
    intro m₀
    obtain ⟨y₀, hy₀, hy₀'⟩ := exists_preimage hω hd (z := rootC (g ^ Fintype.card {a : Fin r // b a = c₀} - 1) ^ m₀)
      (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := g) hd).pow_eq_one, one_pow])
    have hy00 : y₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow (g_pow_sub_pos hd).ne'] at hy₀
      exact zero_ne_one hy₀
    let y : ℕ → (Fbar g)ˣ := fun c => if c = c₀ then Units.mk0 y₀ hy00 else 1
    let m : ℕ → ℕ := fun c => if c = c₀ then m₀ else 0
    have hm : ∀ c, ω (y c) = rootC (g ^ Fintype.card {a : Fin r // b a = c} - 1) ^ m c := by
      intro c
      by_cases hc : c = c₀
      · subst hc
        simpa [y, m] using hy₀'
      · simp [y, m, hc]
    obtain ⟨p, hp⟩ := exists_block b (fun c => (y c : Fbar g)) (by
      intro c _
      by_cases hc : c = c₀
      · subst hc
        simpa [y] using hy₀
      · simp [y, hc])
    have e1 := hL.value x y m p (fun c hc => by rw [hx c hc]; exact minpoly.aeval _ _) hp
      (fun c _ => by rw [he, hm, rootOfOne_eq, blkSize_eq])
    rw [hch, Finset.prod_congr rfl (fun c hc => cuspVal_eq_torusValue ω (card_blk_pos hc) _ (hx₀p c hc) (hp c hc) (hm c)),
      ← Finset.mul_prod_erase _ _ hc₀, ← Finset.mul_prod_erase _ _ hc₀] at e1
    simp only [blkSize_eq, he _] at e1
    have e2 : ∀ z : ℕ → ℂ, ∏ c ∈ (Finset.univ.image b).erase c₀,
        torusValue g (Fintype.card {a : Fin r // b a = c}) (dg (y c : Fbar g)) (z c) (m c) =
        ∏ c ∈ (Finset.univ.image b).erase c₀,
        torusValue g (Fintype.card {a : Fin r // b a = c}) (dg (y c : Fbar g)) 1 0 := by
      intro z
      refine Finset.prod_congr rfl fun c hc => ?_
      simp [torusValue, m, Finset.ne_of_mem_erase hc]
    rw [e2 (fun c => ω (x₀ c)), e2 (fun c => ω (x c))] at e1
    have e3 := mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun c _ => by
      refine mul_ne_zero (torus_coef_ne (dg_pos _)) ?_
      simpa using (dg_pos _).ne') e1
    have e4 := mul_left_cancel₀ (torus_coef_ne (dg_pos _)) e3
    have hyc : (y c₀ : Fbar g) = y₀ := by simp [y]
    have hmc : m c₀ = m₀ := by simp [m]
    rw [hyc, hmc] at e4
    obtain ⟨k, hk⟩ := exists_dg_mul hd hy₀
    have s1 := sum_period (period_of ω hd (hxp _ hc₀) hy₀') k
    have s2 := sum_period (period_of ω hd (hx₀p _ hc₀) hy₀') k
    rw [← hk] at s1 s2
    rw [s1, s2, e4])
  rw [hx _ hc₀]
  exact mem_roots_minpoly.2 ⟨j, hω (by rw [hj, map_pow])⟩

end GlobalTheory.GoodCharsCompare
