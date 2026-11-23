import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

variable (A n) in

abbrev Laurent : Type u := AddMonoidAlgebra A (Fin (n + 1) → ℤ)

variable (n) in

def expHom : (Fin (n + 1) →₀ ℕ) →+ (Fin (n + 1) → ℤ) where
  toFun e j := e j
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

lemma expHom_injective : Function.Injective (expHom n) := fun e e' h => by
  ext j
  have := congrFun h j
  simp only [expHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact_mod_cast this

lemma sum_expHom (e : Fin (n + 1) →₀ ℕ) : ∑ j, expHom n e j = (e.degree : ℤ) := by
  rw [Finsupp.degree_eq_sum]
  push_cast
  rfl

variable (A n) in

def toLaurent : MvPolynomial (Fin (n + 1)) A →+* Laurent A n :=
  AddMonoidAlgebra.mapDomainRingHom A (expHom n)

lemma toLaurent_injective : Function.Injective (toLaurent A n) :=
  AddMonoidAlgebra.mapDomain_injective expHom_injective

lemma toLaurent_monomial (e : Fin (n + 1) →₀ ℕ) (c : A) :
    toLaurent A n (monomial e c) = AddMonoidAlgebra.single (expHom n e) c := by
  rw [← single_eq_monomial]
  exact AddMonoidAlgebra.mapDomain_single

def mult {p : ℕ} (i : Fin p → Fin (n + 1)) : Fin (n + 1) → ℤ := ∑ a, Pi.single (i a) 1

lemma mult_apply {p : ℕ} (i : Fin p → Fin (n + 1)) (j : Fin (n + 1)) :
    mult i j = ((Finset.univ.filter fun a => i a = j).card : ℤ) := by
  simp [mult, Finset.sum_apply, Pi.single_apply, Finset.sum_boole, eq_comm]

lemma mult_eq_zero {p : ℕ} (i : Fin p → Fin (n + 1)) {j : Fin (n + 1)} (hj : j ∉ Set.range i) :
    mult i j = 0 := by
  rw [mult_apply]
  simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun a _ h => hj ⟨a, h⟩

lemma one_le_mult {p : ℕ} (i : Fin p → Fin (n + 1)) {j : Fin (n + 1)} (hj : j ∈ Set.range i) :
    1 ≤ mult i j := by
  obtain ⟨a, rfl⟩ := hj
  rw [mult_apply]
  exact_mod_cast Finset.card_pos.mpr ⟨a, by simp⟩

lemma sum_mult {p : ℕ} (i : Fin p → Fin (n + 1)) : ∑ j, mult i j = p := by
  simp only [mult, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp [Pi.single_apply]

lemma sum_nsmul_mult {p : ℕ} (i : Fin p → Fin (n + 1)) (N : ℕ) :
    ∑ x, (N • mult i) x = (N : ℤ) * p := by
  change ∑ x, N • mult i x = _
  rw [← Finset.smul_sum, sum_mult, nsmul_eq_mul]

lemma toLaurent_X (j : Fin (n + 1)) :
    toLaurent A n (X j) = AddMonoidAlgebra.single (Pi.single j 1) 1 := by
  rw [X, toLaurent_monomial]
  congr 1
  ext j'
  simp [expHom, Finsupp.single_apply, Pi.single_apply, eq_comm]

lemma toLaurent_xprod {p : ℕ} (i : Fin p → Fin (n + 1)) :
    toLaurent A n (xprod i) = AddMonoidAlgebra.single (mult i) 1 := by
  rw [xprod, map_prod]
  simp_rw [toLaurent_X]
  rw [AddMonoidAlgebra.prod_single]
  simp [mult]

lemma single_mul_single_neg (m : Fin (n + 1) → ℤ) :
    (AddMonoidAlgebra.single m (1 : A) : Laurent A n) * AddMonoidAlgebra.single (-m) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  rfl

lemma isUnit_single (m : Fin (n + 1) → ℤ) :
    IsUnit (AddMonoidAlgebra.single m (1 : A) : Laurent A n) :=
  IsUnit.of_mul_eq_one _ (single_mul_single_neg m)

lemma isUnit_toLaurent_xprod {p : ℕ} (i : Fin p → Fin (n + 1)) :
    IsUnit (toLaurent A n (xprod i)) := by
  rw [toLaurent_xprod]
  exact isUnit_single _

def awayToLaurent {p : ℕ} (i : Fin p → Fin (n + 1)) :
    Localization.Away (xprod (A := A) i) →+* Laurent A n :=
  IsLocalization.Away.lift (xprod i) (isUnit_toLaurent_xprod i)

lemma awayToLaurent_algebraMap {p : ℕ} (i : Fin p → Fin (n + 1)) (a : MvPolynomial (Fin (n + 1)) A) :
    awayToLaurent i (algebraMap _ _ a) = toLaurent A n a :=
  IsLocalization.lift_eq _ _

lemma awayToLaurent_mk {p : ℕ} (i : Fin p → Fin (n + 1)) (a : MvPolynomial (Fin (n + 1)) A) (N : ℕ) :
    awayToLaurent i (Localization.mk a (ProjTwist.fpow (xprod i) N)) =
      toLaurent A n a * AddMonoidAlgebra.single (-(N • mult i)) 1 := by
  have h1 : (Localization.mk a (ProjTwist.fpow (xprod i) N) : Localization.Away (xprod (A := A) i)) *
      algebraMap (MvPolynomial (Fin (n + 1)) A) _ (xprod i ^ N) =
      algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i)) a := by
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have h2 := congrArg (awayToLaurent i) h1
  rw [map_mul, awayToLaurent_algebraMap, awayToLaurent_algebraMap, map_pow, toLaurent_xprod,
    AddMonoidAlgebra.single_pow, one_pow] at h2
  rw [← h2, mul_assoc, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul,
    ← AddMonoidAlgebra.one_def, mul_one]

lemma awayToLaurent_injective {p : ℕ} (i : Fin p → Fin (n + 1)) :
    Function.Injective (awayToLaurent (A := A) i) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using Localization.induction_on with
  | H x =>
    obtain ⟨a, ⟨s, N, rfl⟩⟩ := x
    change awayToLaurent i (Localization.mk a (ProjTwist.fpow (xprod i) N)) = 0 at hz
    rw [awayToLaurent_mk] at hz
    have ha : toLaurent A n a = 0 := by
      have := congrArg (· * AddMonoidAlgebra.single (N • mult i) (1 : A)) hz
      simp only [zero_mul, mul_assoc] at this
      rwa [AddMonoidAlgebra.single_mul_single, neg_add_cancel, mul_one, ← AddMonoidAlgebra.one_def,
        mul_one] at this
    rw [← map_zero (toLaurent A n)] at ha
    rw [toLaurent_injective ha]
    exact Localization.mk_zero _

def Allowed (s : Set (Fin (n + 1))) (k : ℤ) (m : Fin (n + 1) → ℤ) : Prop :=
  ∑ j, m j = k ∧ ∀ j, j ∉ s → 0 ≤ m j

lemma Allowed.mono {s t : Set (Fin (n + 1))} {k : ℤ} {m : Fin (n + 1) → ℤ} (h : Allowed s k m)
    (hst : s ⊆ t) : Allowed t k m :=
  ⟨h.1, fun j hj => h.2 j fun hs => hj (hst hs)⟩

variable (A) in

def LDeg (s : Set (Fin (n + 1))) (k : ℤ) : AddSubgroup (Laurent A n) where
  carrier := {ℓ | ∀ m, ℓ.coeff m ≠ 0 → Allowed s k m}
  zero_mem' m h := (h rfl).elim
  add_mem' {a b} ha hb m h := by
    by_cases h1 : a.coeff m = 0
    · refine hb m fun h2 => h ?_
      simp [AddMonoidAlgebra.coeff_add, h1, h2]
    · exact ha m h1
  neg_mem' {a} ha m h := ha m fun h1 => h (by simp [AddMonoidAlgebra.coeff_neg, h1])

lemma LDeg_mono {s t : Set (Fin (n + 1))} (hst : s ⊆ t) (k : ℤ) : LDeg A s k ≤ LDeg A t k :=
  fun _ hℓ m hm => (hℓ m hm).mono hst

lemma single_mem_LDeg {s : Set (Fin (n + 1))} {k : ℤ} {m : Fin (n + 1) → ℤ} (hm : Allowed s k m)
    (c : A) : AddMonoidAlgebra.single m c ∈ LDeg A s k := by
  classical
  intro m' h
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h
  split_ifs at h with he
  · exact he ▸ hm
  · exact (h rfl).elim

lemma coeff_toLaurent_eq_zero {a : MvPolynomial (Fin (n + 1)) A} {m : Fin (n + 1) → ℤ}
    (hm : m ∉ Set.range (expHom n)) : (toLaurent A n a).coeff m = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ hm

lemma coeff_toLaurent_expHom (a : MvPolynomial (Fin (n + 1)) A) (e : Fin (n + 1) →₀ ℕ) :
    (toLaurent A n a).coeff (expHom n e) = a.coeff e :=
  Finsupp.mapDomain_apply expHom_injective _ _

theorem mem_LDeg_iff {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (ℓ : Laurent A n) :
    ℓ ∈ LDeg A (Set.range i) k ↔
      ∃ z ∈ ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k,
        awayToLaurent i z = ℓ := by
  classical
  constructor
  · intro hℓ
    let G := (ProjTwist.awayDeg (grading A n) (xprod_mem (A := A) i) (Nat.succ_pos p) k).map
      (awayToLaurent i).toAddMonoidHom
    suffices h : ∀ ℓ ∈ LDeg A (Set.range i) k, ℓ ∈ G by
      obtain ⟨z, hz, rfl⟩ := h ℓ hℓ
      exact ⟨z, hz, rfl⟩
    intro ℓ hℓ
    have hsum : ℓ = ∑ m ∈ ℓ.coeff.support, AddMonoidAlgebra.single m (ℓ.coeff m) := by
      apply AddMonoidAlgebra.coeff_injective
      rw [AddMonoidAlgebra.coeff_sum]
      simp only [AddMonoidAlgebra.coeff_single]
      exact (Finsupp.sum_single ℓ.coeff).symm
    rw [hsum]
    refine G.sum_mem fun m hm => ?_
    have hA : Allowed (Set.range i) k m := hℓ m (Finsupp.mem_support_iff.mp hm)
    set c := ℓ.coeff m
    set N : ℕ := ∑ j, (m j).natAbs
    have hN : ∀ j, ((m j).natAbs : ℤ) ≤ N := fun j => by
      exact_mod_cast Finset.single_le_sum (f := fun j => (m j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have hpos : ∀ j, 0 ≤ m j + N * mult i j := fun j => by
      by_cases hj : j ∈ Set.range i
      · have h1 := one_le_mult i hj
        have h2 := hN j
        have h3 : -(m j) ≤ ((m j).natAbs : ℤ) := by omega
        nlinarith
      · rw [mult_eq_zero i hj, mul_zero, add_zero]
        exact hA.2 j hj
    let e : Fin (n + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (m j + N * mult i j).toNat
    have hexp : expHom n e = m + N • mult i := by
      funext j
      change ((m j + N * mult i j).toNat : ℤ) = m j + N • mult i j
      rw [nsmul_eq_mul]
      exact Int.toNat_of_nonneg (hpos j)
    have hdeg : (e.degree : ℤ) = N * (p + 1 : ℕ) + k := by
      rw [← sum_expHom, hexp]
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_nsmul_mult, hA.1]
      ring
    refine ⟨Localization.mk (monomial e c) (ProjTwist.fpow (xprod i) N),
      ProjTwist.mk_mem_awayDeg _ _ (isHomogeneous_monomial c rfl) hdeg, ?_⟩
    change awayToLaurent i _ = _
    rw [awayToLaurent_mk, toLaurent_monomial, AddMonoidAlgebra.single_mul_single, hexp, mul_one,
      add_neg_cancel_right]
  · rintro ⟨z, ⟨N, j, a, ha, hj, rfl⟩, rfl⟩ m hm
    rw [awayToLaurent_mk, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, neg_neg] at hm
    by_cases hr : m + N • mult i ∈ Set.range (expHom n)
    · obtain ⟨e, he⟩ := hr
      rw [← he, coeff_toLaurent_expHom] at hm
      have hdeg : (e.degree : ℤ) = j := by
        have := ha hm
        rw [Finsupp.degree_eq_weight_one]
        exact_mod_cast this
      have hm' : m = expHom n e - N • mult i := by rw [he]; abel
      refine ⟨?_, fun j' hj' => ?_⟩
      · have hs := sum_nsmul_mult i N
        rw [hm']
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_expHom, hdeg, hj, hs]
        ring
      · rw [hm']
        simp [mult_eq_zero i hj', expHom]
    · exact (hm (coeff_toLaurent_eq_zero hr)).elim

lemma isUnit_algebraMap_xprod {p q : ℕ} {i : Fin p → Fin (n + 1)} {i' : Fin q → Fin (n + 1)}
    (h : Set.range i ⊆ Set.range i') :
    IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i'))
      (xprod i)) := by
  rw [show xprod (A := A) i = ∏ a, X (i a) from rfl, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => ?_
  obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
  refine isUnit_of_dvd_unit ?_ (IsLocalization.Away.algebraMap_isUnit (xprod (A := A) i'))
  rw [← hb]
  exact map_dvd _ (Finset.dvd_prod_of_mem (fun c => X (i' c)) (Finset.mem_univ b))

lemma locMap_eq_of_awayToLaurent_eq {p q : ℕ} {i : Fin p → Fin (n + 1)}
    {i' : Fin q → Fin (n + 1)} (h : Set.range i ⊆ Set.range i')
    {z : Localization.Away (xprod (A := A) i)} {z' : Localization.Away (xprod (A := A) i')}
    (hzz : awayToLaurent i z = awayToLaurent i' z') (x : ProjectiveSpectrum (grading A n))
    (hx : xprod i ∉ x.asHomogeneousIdeal) (hx' : xprod i' ∉ x.asHomogeneousIdeal) :
    ProjTwist.locMap x hx z = ProjTwist.locMap x hx' z' := by
  let can : Localization.Away (xprod (A := A) i) →+* Localization.Away (xprod (A := A) i') :=
    IsLocalization.Away.lift (xprod i) (isUnit_algebraMap_xprod h)
  have hcan : can.comp (algebraMap _ _) = algebraMap _ _ := IsLocalization.lift_comp _
  have h1 : (awayToLaurent i').comp can = awayToLaurent i := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (xprod (A := A) i))
    rw [RingHom.comp_assoc, hcan]
    ext a
    · simp [awayToLaurent_algebraMap]
    · simp [awayToLaurent_algebraMap]
  have h2 : can z = z' := awayToLaurent_injective i' (by rw [← hzz, ← h1]; rfl)
  rw [← h2]
  exact (ProjTwist.locMap_comp can hcan x hx' hx z).symm

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
