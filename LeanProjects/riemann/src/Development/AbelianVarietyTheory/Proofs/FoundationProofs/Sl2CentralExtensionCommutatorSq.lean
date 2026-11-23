import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.SLTwoCentral

noncomputable def red (p a : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ (a + 1))) →*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) (ZMod p))

end GlobalTheory.SLTwoCentral

namespace GlobalTheory

open scoped MatrixGroups TensorProduct in
open Matrix in
private theorem pow_card_div_orderOf_eq_one_of_mem_ker_commutator {E G : Type} [Group E] [Group G]
    [Finite G] (π : E →* G) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center E) (g : G) (x : E) (hx : x ∈ π.ker) (hc : x ∈ commutator E) :
    x ^ (Nat.card G / orderOf g) = 1 := by
  set A := (Subgroup.zpowers g).comap π with hAdef
  obtain ⟨e, he⟩ := hπ g
  have key : ∀ a ∈ A, ∃ i : ℤ, ∃ k ∈ π.ker, a = e ^ i * k := by
    intro a ha
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp ha)
    refine ⟨i, (e ^ i)⁻¹ * a, ?_, by group⟩
    simp [MonoidHom.mem_ker, map_zpow, he, hi]
  have hA : ∀ a b : A, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, k, hk, rfl⟩ := key a ha
    obtain ⟨j, m, hm, rfl⟩ := key b hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hkc := Subgroup.mem_center_iff.mp (hK hk)
    have hmc := Subgroup.mem_center_iff.mp (hK hm)
    calc e ^ i * k * (e ^ j * m) = e ^ i * e ^ j * (k * m) := by
          rw [mul_assoc, mul_assoc, ← mul_assoc k, ← hkc (e ^ j), mul_assoc]
      _ = e ^ j * e ^ i * (m * k) := by
          rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm, (hmc k).symm]
      _ = e ^ j * m * (e ^ i * k) := by
          rw [mul_assoc, mul_assoc, ← mul_assoc m, ← hmc (e ^ i), mul_assoc]
  have hidx : A.index = Nat.card G / orderOf g := by
    rw [hAdef, Subgroup.index_comap_of_surjective _ hπ, ← Nat.card_zpowers,
      ← (Subgroup.zpowers g).card_mul_index, Nat.mul_div_cancel_left _ Nat.card_pos]
  haveI : A.FiniteIndex := ⟨by
    rw [hAdef, Subgroup.index_comap_of_surjective _ hπ]; exact Subgroup.index_ne_zero_of_finite⟩
  rw [← hidx]
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hA }
  have h1 := Abelianization.commutator_subset_ker ((MonoidHom.id A).transfer (H := A)) hc
  rw [MonoidHom.mem_ker, MonoidHom.transfer_eq_pow (MonoidHom.id A) x] at h1
  · simpa using congrArg Subtype.val h1
  · intro k g₀ _
    have : x ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ (hK hx) k
    rw [mul_assoc, (Subgroup.mem_center_iff.mp this g₀).symm, ← mul_assoc, inv_mul_cancel, one_mul]

open scoped MatrixGroups TensorProduct in
open Matrix in
private theorem exists_card_ker_red_eq_prime_pow (p b : ℕ) [Fact p.Prime] :
    ∃ k, Nat.card (_root_.GlobalTheory.SLTwoCentral.red p b).ker = p ^ k := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdiv : ∀ z : ZMod (p ^ (b + 1)),
      ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero b)) (ZMod p) z = 0 →
        ∃ w : ZMod (p ^ (b + 1)), z = p * w := by
    intro z hz
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hz
    obtain ⟨w, hw⟩ := (ZMod.natCast_eq_zero_iff _ p).mp hz
    exact ⟨w, by rw [← ZMod.natCast_zmod_val z, hw]; push_cast; ring⟩
  have binom : ∀ (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) (r : ℕ),
      (A + 1) ^ (r + 2) = 1 + A * ((r + 2 : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) +
        A ^ 2 * ∑ m ∈ Finset.range (r + 1), A ^ m * ((r + 2).choose (m + 2) : Matrix _ _ _) := by
    intro A r
    rw [(Commute.one_right A).add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Finset.mul_sum]
    have : ∀ m, A ^ (m + 1 + 1) * ((r + 2).choose (m + 1 + 1) : Matrix _ _ _) =
        A ^ 2 * (A ^ m * ((r + 2).choose (m + 2) : Matrix _ _ _)) := by
      intro m; rw [← mul_assoc, ← pow_add]; ring_nf
    simp only [this]
    rw [pow_one, Nat.choose_one_right]
    abel
  obtain ⟨r, hr⟩ : ∃ r, p = r + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have step : ∀ (j : ℕ) (Y : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))), ∃ Y',
      ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1) ^ p = (p : ZMod (p ^ (b + 1))) ^ (j + 2) • Y' + 1 := by
    intro j Y
    have e1 : ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1) ^ p =
        ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1) ^ (r + 2) := by rw [← hr]
    rw [e1, binom]
    set S := ∑ m ∈ Finset.range (r + 1), ((p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y) ^ m *
      ((r + 2).choose (m + 2) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1))))
    refine ⟨Y + (p : ZMod (p ^ (b + 1))) ^ j • (Y ^ 2 * S), ?_⟩
    rw [← hr, ← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul (ZMod (p ^ (b + 1))), smul_pow,
      smul_mul_assoc, smul_smul, smul_add, smul_smul]
    have c1 : (p : ZMod (p ^ (b + 1))) * (p : ZMod (p ^ (b + 1))) ^ (j + 1) =
        (p : ZMod (p ^ (b + 1))) ^ (j + 2) := by ring
    have c2 : ((p : ZMod (p ^ (b + 1))) ^ (j + 1)) ^ 2 =
        (p : ZMod (p ^ (b + 1))) ^ (j + 2) * (p : ZMod (p ^ (b + 1))) ^ j := by ring
    rw [c1, c2]
    abel
  have hpow : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ (b + 1))),
      _root_.GlobalTheory.SLTwoCentral.red p b g = 1 → ∀ j, ∃ Y,
        (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) ^ (p ^ j) =
          (p : ZMod (p ^ (b + 1))) ^ (j + 1) • Y + 1 := by
    intro g hg j
    induction j with
    | zero =>
      have hent : ∀ i k, ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero b)) (ZMod p)
          (((g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) - 1) i k) = 0 := by
        intro i k
        have h1 := congrFun (congrFun (congrArg Subtype.val hg) i) k
        have h2 := congrFun (congrFun (Matrix.map_one
          (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero b)) (ZMod p)) (map_zero _) (map_one _)) i) k
        rw [Matrix.sub_apply, map_sub, sub_eq_zero]
        exact h1.trans (by rw [Matrix.SpecialLinearGroup.coe_one]; exact h2.symm)
      refine ⟨Matrix.of fun i k => Classical.choose (hdiv _ (hent i k)), ?_⟩
      rw [pow_zero, pow_one, zero_add, pow_one, ← sub_eq_iff_eq_add]
      ext i k
      rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      exact Classical.choose_spec (hdiv _ (hent i k))
    | succ j ih =>
      obtain ⟨Y, hY⟩ := ih
      rw [show p ^ (j + 1) = p ^ j * p from pow_succ p j, pow_mul, hY]
      exact step j Y
  have hP : IsPGroup p (_root_.GlobalTheory.SLTwoCentral.red p b).ker := by
    rintro ⟨g, hg⟩
    refine ⟨b, Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨Y, hY⟩ := hpow g hg b
    have h0 : (p : ZMod (p ^ (b + 1))) ^ (b + 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    change (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (b + 1)))) ^ (p ^ b) = 1
    rw [hY, h0, zero_smul, zero_add]
  exact IsPGroup.iff_card.mp hP

open scoped MatrixGroups TensorProduct in
open Matrix in
private theorem card_sl2_zmod_mul_pred (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  set D := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod p)
  have hdet : ∀ g : GL (Fin 2) (ZMod p), D g = 1 ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    intro g
    rw [← Units.val_eq_one]
    rfl
  have e : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ≃ D.ker :=
    { toFun := fun A => ⟨Matrix.SpecialLinearGroup.toGL A, (hdet _).mpr A.2⟩
      invFun := fun g => ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)), (hdet g.1).mp g.2⟩
      left_inv := fun A => rfl
      right_inv := fun g => Subtype.ext (Units.ext rfl) }
  have hrange : Nat.card D.range = p - 1 := by
    rw [MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card_units]
  rw [Nat.card_congr e, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index, Matrix.card_GL_field,
    Fin.prod_univ_two, ZMod.card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]

open scoped MatrixGroups TensorProduct in
open Matrix in
private theorem exists_orderOf_eq_succ_sl2_zmod (p : ℕ) [Fact p.Prime] :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), orderOf h = p + 1 := by
  have hp := (Fact.out : p.Prime)
  classical
  set K := GaloisField p 2
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := hp.one_le
    zify [this, Nat.one_le_pow 2 p hp.pos]
    ring
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hunits : Nat.card Kˣ = p ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
  set ζ : K := (γ : K) ^ (p - 1)
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hζ : orderOf ζ = p + 1 := by
    rw [orderOf_pow_of_dvd hp1, orderOf_units, hγ, hunits, hsq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp1)]
    rw [orderOf_units, hγ, hunits, hsq]; exact dvd_mul_right _ _
  have hnorm : Algebra.norm (ZMod p) ζ = 1 := by
    apply (algebraMap (ZMod p) K).injective
    rw [FiniteField.algebraMap_norm_eq_pow, hcard, Nat.card_zmod, hsq,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp1), map_one, ← hζ, pow_orderOf_eq_one]
  let b := Module.finBasisOfFinrankEq (ZMod p) K (GaloisField.finrank p (n := 2) (by norm_num))
  have hdet : (Algebra.leftMulMatrix b ζ).det = 1 := by rw [← Algebra.norm_eq_matrix_det, hnorm]
  let h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨Algebra.leftMulMatrix b ζ, hdet⟩
  refine ⟨h, ?_⟩
  rw [← hζ]
  refine orderOf_eq_orderOf_iff.mpr fun n => ?_
  have hval : h ^ n = 1 ↔ (h : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n = 1 := by
    constructor <;> intro H
    · rw [← Matrix.SpecialLinearGroup.coe_pow, H]; rfl
    · exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, H]; rfl)
  rw [hval]
  change (Algebra.leftMulMatrix b ζ) ^ n = 1 ↔ _
  rw [← map_pow, ← map_one (Algebra.leftMulMatrix b), (Algebra.leftMulMatrix_injective b).eq_iff]

open scoped MatrixGroups TensorProduct in
open Matrix in
private theorem exists_orderOf_eq_pred_sl2_zmod (p : ℕ) [Fact p.Prime] :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), orderOf h = p - 1 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdet : (Matrix.diagonal ![(γ : ZMod p), ((γ⁻¹ : (ZMod p)ˣ) : ZMod p)]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    exact γ.mul_inv
  let h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨_, hdet⟩
  refine ⟨h, ?_⟩
  rw [← hunits, ← hγ]
  refine orderOf_eq_orderOf_iff.mpr fun n => ?_
  have hval : h ^ n = 1 ↔ (h : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n = 1 := by
    constructor <;> intro H
    · rw [← Matrix.SpecialLinearGroup.coe_pow, H]; rfl
    · exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, H]; rfl)
  rw [hval]
  change (Matrix.diagonal _) ^ n = 1 ↔ _
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff, ← Units.val_eq_one,
    Units.val_pow_eq_pow_val]
  constructor
  · intro H; exact H 0
  · intro H i
    have hγn : γ ^ n = 1 := Units.val_eq_one.mp (by rw [Units.val_pow_eq_pow_val]; exact H)
    fin_cases i
    · exact H
    · change ((γ⁻¹ : (ZMod p)ˣ) : ZMod p) ^ n = 1
      rw [← Units.val_pow_eq_pow_val, inv_pow, hγn, inv_one, Units.val_one]

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.sl2_zmod_central_ext_commutator_sq_eq_one :
    ∀ (l n p a : ℕ), l.Prime → p.Prime → 5 ≤ p → p ≠ l → ∀ (E : Type) [Group E]
      (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ a))), Function.Surjective π →
      π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) →
      ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  intro l n p a hl hp hp5 hpl E _ π hπ hK hexp x hx hc
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow := fun g => pow_card_div_orderOf_eq_one_of_mem_ker_commutator π hπ hK g x hx hc
  have hd : orderOf x ∣ l ^ n := orderOf_dvd_of_pow_eq_one (hexp x hx)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp hd
  have hcop : ∀ m, Nat.Coprime (orderOf x) (p ^ m) := fun m => by
    rw [hj]; exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hl hp).mpr hpl.symm)
  rcases a with _ | b
  · have h1 := hpow 1
    haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ 0))) :=
      ⟨fun A B => Subtype.ext (funext fun i => funext fun j => Subsingleton.elim _ _)⟩
    rw [orderOf_one, Nat.div_one, Nat.card_of_subsingleton (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ 0))), pow_one] at h1
    rw [h1, one_pow]
  set G := Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ (b + 1)))
  have hred : Function.Surjective (_root_.GlobalTheory.SLTwoCentral.red p b) :=
    _root_.GlobalTheory.specialLinearGroup_map_surjective (ZMod.castHom_surjective _)
  obtain ⟨k, hk⟩ := exists_card_ker_red_eq_prime_pow p b
  have hcardG : Nat.card G = p ^ k * (p * (p + 1) * (p - 1)) := by
    have hSL := card_sl2_zmod_mul_pred p
    have hSL' : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p + 1) * (p - 1) := by
      have h1 : 0 < p - 1 := by omega
      apply Nat.eq_of_mul_eq_mul_right h1
      rw [hSL]
      have := hp.one_le
      zify [this, Nat.one_le_pow 2 p hp.pos, Nat.pow_le_pow_left this 2, Nat.le_self_pow two_ne_zero p]
      ring
    rw [← hk, ← hSL', ← (_root_.GlobalTheory.SLTwoCentral.red p b).ker.card_mul_index, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hred, Subgroup.card_top]
  have hdiv : ∀ c : ℕ, (∃ h : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), orderOf h = c) →
      orderOf x * c ∣ Nat.card G := by
    rintro c ⟨h, rfl⟩
    obtain ⟨g, rfl⟩ := hred h
    have hxg : orderOf x ∣ Nat.card G / orderOf g := orderOf_dvd_of_pow_eq_one (hpow g)
    have hg : orderOf g ∣ Nat.card G := orderOf_dvd_natCard g
    exact (Nat.mul_dvd_mul_left _ (orderOf_map_dvd _ g)).trans (by rw [mul_comm]; exact Nat.mul_dvd_of_dvd_div hg hxg)
  have hplus := hdiv _ (exists_orderOf_eq_succ_sl2_zmod p)
  have hminus := hdiv _ (exists_orderOf_eq_pred_sl2_zmod p)
  rw [hcardG] at hplus hminus
  have hA : orderOf x ∣ p - 1 := by
    have : orderOf x ∣ p ^ (k + 1) * (p - 1) := by
      apply Nat.dvd_of_mul_dvd_mul_right (show 0 < p + 1 by omega)
      calc orderOf x * (p + 1) ∣ p ^ k * (p * (p + 1) * (p - 1)) := hplus
        _ = p ^ (k + 1) * (p - 1) * (p + 1) := by ring
    exact (hcop (k + 1)).dvd_of_dvd_mul_left this
  have hB : orderOf x ∣ p + 1 := by
    have : orderOf x ∣ p ^ (k + 1) * (p + 1) := by
      apply Nat.dvd_of_mul_dvd_mul_right (show 0 < p - 1 by omega)
      calc orderOf x * (p - 1) ∣ p ^ k * (p * (p + 1) * (p - 1)) := hminus
        _ = p ^ (k + 1) * (p + 1) * (p - 1) := by ring
    exact (hcop (k + 1)).dvd_of_dvd_mul_left this
  have h2 : orderOf x ∣ 2 := by
    have := Nat.dvd_sub hB hA
    rwa [show p + 1 - (p - 1) = 2 by omega] at this
  exact orderOf_dvd_iff_pow_eq_one.mp h2

end GlobalTheory
