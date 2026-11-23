import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowPrimeRangeEqIteratedDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMulStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionFiniteKerRangeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormDifferenceIndexIdentityStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexRangeKerIterateEndomorphismStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem herbPhi_arith (q h0 h1 a t bI bT cI cT i c : ℕ) (hi : i ≠ 0) (hcT : cT ≠ 0)
    (e1 : a * bT * cT = bI * cI * t) (e2 : cI * c ^ q = i ^ q * cT)
    (e3 : h0 * i * bT = bI * h1 * c) :
    h0 ^ q * a * bT ^ (q + 1) = h1 ^ q * t * bI ^ (q + 1) := by
  have hne : i ^ q * cT ≠ 0 := mul_ne_zero (pow_ne_zero _ hi) hcT
  apply mul_right_cancel₀ hne
  calc h0 ^ q * a * bT ^ (q + 1) * (i ^ q * cT) = (h0 * i * bT) ^ q * (a * bT * cT) := by ring
    _ = (bI * h1 * c) ^ q * (bI * cI * t) := by rw [e1, e3]
    _ = h1 ^ q * t * bI ^ (q + 1) * (cI * c ^ q) := by ring
    _ = _ := by rw [e2]

theorem herbPhi_nrm_dif {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n (dif σ a) = σ^[n] a / a := by
  induction n with
  | zero => simp [nrm_apply]
  | succ n ih =>
    rw [nrm_apply] at ih ⊢
    rw [Finset.prod_range_succ, ih, dif_apply, iterate_map_div, Function.iterate_succ_apply,
      mul_comm, div_mul_div_cancel]

theorem herbPhi_stable (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A) (hp : p.Prime)
    (C : Subgroup A) (hst : ∀ x ∈ C, σ x ∈ C) (hn : ∀ x ∈ C, nrm σ p x = 1)
    (hI : pIdx p C ≠ 0) (hT : pTor p C ≠ 0) :
    (C.map (dif σ)).relIndex C ≠ 0 ∧ Nat.card ↥(C ⊓ fix σ) ≠ 0 ∧
      pIdx p C * Nat.card ↥(C ⊓ fix σ) ^ (p - 1) =
        (C.map (dif σ)).relIndex C ^ (p - 1) * pTor p C := by
  let τ : C →* C := (σ.comp C.subtype).codRestrict C (fun x => hst x x.2)
  have hτ : ∀ x : C, (τ x : A) = σ x := fun x => rfl
  have hit : ∀ (k : ℕ) (x : C), ((τ^[k] x : C) : A) = σ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  let lam : Monoid.End C := dif τ
  have hnτ : ∀ a, nrm τ p a = 1 := by
    intro a
    apply Subtype.ext
    have := hn a a.2
    rw [nrm_apply] at this ⊢
    rw [SubmonoidClass.coe_finset_prod]
    simp only [hit]
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.T.pow_prime_range_eq_iterated_difference p C τ lam hp (fun _ => rfl) hnτ
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = k + 1 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [hk] at h1 h2 ⊢
  have eI : pIdx p C = (MonoidHom.range (lam ^ (k + 1) : Monoid.End C)).index := by
    rw [← h1, pIdx, Subgroup.relIndex]
    congr 1
    ext x
    simp only [pows, Subgroup.mem_subgroupOf, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext e⟩
    · rintro ⟨y, -, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have eT : pTor p C = Nat.card (MonoidHom.ker (lam ^ (k + 1) : Monoid.End C)) := by
    rw [pTor]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, (h2 _).1 (Subtype.ext x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val ((h2 _).2 y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  have ei : (C.map (dif σ)).relIndex C = (MonoidHom.range lam).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
    · rintro ⟨y, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have ec : Nat.card ↥(C ⊓ fix σ) = Nat.card (MonoidHom.ker lam) := by
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (div_eq_one.2 x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, div_eq_one.1 (congrArg Subtype.val y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  rw [eI] at hI ⊢
  rw [eT] at hT ⊢
  rw [ei, ec]
  exact GlobalTheory.T.index_range_ker_iterate_endomorphism C lam k hI hT

theorem herbrand_prime_order : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), p.Prime → (∀ a, σ^[p] a = a) → pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → (nrm σ p).range.relIndex (fix σ) ≠ 0 ∧ (dif σ).range.relIndex (nrm σ p).ker ≠ 0 ∧ pIdx p (fix σ) ≠ 0 ∧ pTor p (fix σ) ≠ 0 ∧ (nrm σ p).range.relIndex (fix σ) ^ (p - 1) * pIdx p (⊤ : Subgroup A) * pTor p (fix σ) ^ p = (dif σ).range.relIndex (nrm σ p).ker ^ (p - 1) * pTor p (⊤ : Subgroup A) * pIdx p (fix σ) ^ p := by
  intro p A _ σ hp hσ ha ht
  have hker : (dif σ).ker = fix σ := by
    ext x
    rw [MonoidHom.mem_ker, dif_apply, div_eq_one, mem_fix]
  have hcT : pTor p (dif σ).range ≠ 0 := by
    unfold pTor at ht ⊢
    have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero ht
    have : Finite {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} :=
      Finite.of_injective (β := {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1})
        (fun x => ⟨x.1, trivial, x.2.2⟩) (fun x y h => Subtype.ext (by simpa using h))
    have : Nonempty {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow _⟩⟩
    exact Nat.card_pos.ne'
  obtain ⟨hbI, hbT, hcI⟩ := GlobalTheory.T.powIndex_torsion_finite_ker_range p A A (dif σ) ha ht hcT
  obtain ⟨-, -, e1⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p A A (dif σ) hbI hbT hcI hcT
  rw [hker] at hbI hbT e1
  obtain ⟨hi, hc, e2⟩ := herbPhi_stable p A σ hp (dif σ).range
    (by rintro _ ⟨y, rfl⟩; exact ⟨σ y, by rw [dif_apply, dif_apply, _root_.map_div]⟩)
    (by rintro _ ⟨y, rfl⟩; rw [herbPhi_nrm_dif, hσ, div_self']) hcI hcT
  have e3 := GlobalTheory.T.norm_difference_index_identity p A σ hσ
  have hle : pows p (fix σ) ≤ (nrm σ p).range := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_⟩
    have hy' : σ y = y := hy
    rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed hy' i)]
    simp
  have h0 : (nrm σ p).range.relIndex (fix σ) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hbI (Subgroup.relIndex_dvd_of_le_left _ hle)
  have h1 : (dif σ).range.relIndex (nrm σ p).ker ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at e3
    exact mul_ne_zero (mul_ne_zero h0 hi) hbT e3
  refine ⟨h0, h1, hbI, hbT, ?_⟩
  have := herbPhi_arith (p - 1) _ _ _ _ _ _ _ _ _ _ hi hcT e1 e2 e3
  rwa [Nat.sub_add_cancel hp.one_le] at this

end GlobalTheory.CNorm
