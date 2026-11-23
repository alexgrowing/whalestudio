import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqIteratePrimeCharP
open IsLocalRing GlobalTheory.FormalOrigin

noncomputable section
namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterOp_succ {A : Type} {n : ℕ} (ds : Fin (n+1) → A → A) (α : Fin (n+1) →₀ ℕ) (f : A) :
    iterOp ds α f = (ds 0)^[α 0] (iterOp (fun i => ds i.succ) α.tail f) := by
  unfold iterOp
  rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
  congr 1

def iterHom {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) : A →+ A where
  toFun := (⇑D)^[k]
  map_zero' := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  map_add' x y := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add, Function.iterate_succ_apply',
        Function.iterate_succ_apply']

theorem iterHom_apply {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) (x : A) :
    iterHom D k x = (⇑D)^[k] x := rfl

theorem exists_iterOpHom {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ),
    ∃ F : A →+ A, ∀ x, F x = iterOp (fun i => ⇑(ds i)) α x
  | 0, ds, α => ⟨AddMonoidHom.id A, fun x => by
      have : α = 0 := Subsingleton.elim _ _
      subst this; rw [iterOp_zero]; rfl⟩
  | n+1, ds, α => by
      obtain ⟨F, hF⟩ := exists_iterOpHom (fun i => ds i.succ) α.tail
      exact ⟨(iterHom (ds 0) (α 0)).comp F, fun x => by
        rw [iterOp_succ, AddMonoidHom.comp_apply, iterHom_apply, hF]⟩

theorem sum_antidiagonal_succ {M : Type} [AddCommMonoid M] {n : ℕ} (α : Fin (n+1) →₀ ℕ)
    (F : (Fin (n+1) →₀ ℕ) → (Fin (n+1) →₀ ℕ) → M) :
    ∑ p ∈ antidiagonal α, F p.1 p.2 =
      ∑ q ∈ antidiagonal (α 0), ∑ r ∈ antidiagonal α.tail,
        F (Finsupp.cons q.1 r.1) (Finsupp.cons q.2 r.2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ((p.1 0, p.2 0), (p.1.tail, p.2.tail)))
    (fun x => (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p1, p2⟩ h
    simp only [mem_coe, HasAntidiagonal.mem_antidiagonal] at h
    simp only [mem_coe, mem_product, HasAntidiagonal.mem_antidiagonal]
    subst h
    refine ⟨by simp, ?_⟩
    ext i; simp [Finsupp.tail_apply]
  · rintro ⟨⟨j, k⟩, ⟨r1, r2⟩⟩ h
    simp only [mem_coe, mem_product, HasAntidiagonal.mem_antidiagonal] at h
    simp only [mem_coe, HasAntidiagonal.mem_antidiagonal]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h.1]
    · have := DFunLike.congr_fun h.2 i
      simpa [Finsupp.tail_apply] using this
  · rintro ⟨p1, p2⟩ _
    simp [Finsupp.cons_tail]
  · rintro ⟨⟨j, k⟩, ⟨r1, r2⟩⟩ _
    simp [Finsupp.tail_cons]
  · rintro ⟨p1, p2⟩ _
    simp [Finsupp.cons_tail]

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterOp_mul {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) (f g : A),
    iterOp (fun i => ⇑(ds i)) α (f * g) = ∑ p ∈ antidiagonal α,
      (∏ i, (α i).choose (p.1 i)) • (iterOp (fun i => ⇑(ds i)) p.1 f * iterOp (fun i => ⇑(ds i)) p.2 g)
  | 0, ds, α, f, g => by
      have : α = 0 := Subsingleton.elim _ _
      subst this
      simp [iterOp_zero]
  | n+1, ds, α, f, g => by
      have ih := iterOp_mul (fun i => ds i.succ) α.tail f g
      have hs : ∀ (β : Fin (n+1) →₀ ℕ) x, iterOp (fun i => ⇑(ds i)) β x =
          (⇑(ds 0))^[β 0] (iterOp (fun i => ⇑(ds i.succ)) β.tail x) := fun β x => iterOp_succ _ β x
      rw [hs, ih, ← iterHom_apply, map_sum, sum_antidiagonal_succ α (fun a b => (∏ i, (α i).choose (a i)) •
        (iterOp (fun i => ⇑(ds i)) a f * iterOp (fun i => ⇑(ds i)) b g))]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_nsmul, iterHom_apply, GlobalTheory.derivation_iterate_leibniz, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs, hs, Fin.prod_univ_succ]
      simp only [Finsupp.cons_zero, Finsupp.tail_cons, Finsupp.cons_succ, Finsupp.tail_apply]
      rw [← nsmul_eq_mul, smul_smul, mul_comm]

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterate_one {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) :
    (⇑D)^[k] 1 = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Function.iterate_succ_apply, D.map_one_eq_zero, ← iterHom_apply, map_zero]
    simp

theorem eq_zero_iff_succ {n : ℕ} (α : Fin (n+1) →₀ ℕ) : α = 0 ↔ α 0 = 0 ∧ α.tail = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, by ext i; simp [Finsupp.tail_apply]⟩
  · rintro ⟨h0, ht⟩
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0
    · have := DFunLike.congr_fun ht i
      simpa [Finsupp.tail_apply] using this

theorem iterOp_one {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ),
    iterOp (fun i => ⇑(ds i)) α 1 = if α = 0 then 1 else 0
  | 0, ds, α => by
      have : α = 0 := Subsingleton.elim _ _
      subst this
      simp [iterOp_zero]
  | n+1, ds, α => by
      have ih := iterOp_one (fun i => ds i.succ) α.tail
      have hs : ∀ (β : Fin (n+1) →₀ ℕ) x, iterOp (fun i => ⇑(ds i)) β x =
          (⇑(ds 0))^[β 0] (iterOp (fun i => ⇑(ds i.succ)) β.tail x) := fun β x => iterOp_succ _ β x
      rw [hs, ih]
      by_cases ht : α.tail = 0
      · rw [if_pos ht, iterate_one]
        simp [eq_zero_iff_succ α, ht]
      · rw [if_neg ht, ← iterHom_apply, map_zero]
        simp [eq_zero_iff_succ α, ht]

theorem iterOp_add {A : Type} [CommRing A] {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) (f g : A) :
    iterOp (fun i => ⇑(ds i)) α (f + g) = iterOp (fun i => ⇑(ds i)) α f + iterOp (fun i => ⇑(ds i)) α g := by
  obtain ⟨F, hF⟩ := exists_iterOpHom ds α
  rw [← hF, ← hF, ← hF, map_add]

theorem iterOp_zero' {A : Type} [CommRing A] {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) :
    iterOp (fun i => ⇑(ds i)) α 0 = 0 := by
  obtain ⟨F, hF⟩ := exists_iterOpHom ds α
  rw [← hF, map_zero]

theorem factor_identity {n : ℕ} (α : Fin n →₀ ℕ) (p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ)) (hp : p.1 + p.2 = α) :
    (∏ i, ((α i).factorial : ℚ))⁻¹ * ((∏ i, (α i).choose (p.1 i) : ℕ) : ℚ) =
      (∏ i, ((p.1 i).factorial : ℚ))⁻¹ * (∏ i, ((p.2 i).factorial : ℚ))⁻¹ := by
  have hfac : ∀ i, ((α i).choose (p.1 i) : ℚ) * (((p.1 i).factorial : ℚ) * ((p.2 i).factorial : ℚ)) =
      ((α i).factorial : ℚ) := by
    intro i
    have e : α i = p.1 i + p.2 i := by rw [← hp]; rfl
    have h2 : p.2 i = α i - p.1 i := by omega
    have := Nat.choose_mul_factorial_mul_factorial (n := α i) (k := p.1 i) (by omega)
    rw [← h2] at this
    rw [← mul_assoc]
    exact_mod_cast this
  have hprod : (∏ i, ((α i).choose (p.1 i) : ℚ)) *
      ((∏ i, ((p.1 i).factorial : ℚ)) * ∏ i, ((p.2 i).factorial : ℚ)) = ∏ i, ((α i).factorial : ℚ) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hfac i
  have h1 : (∏ i, ((p.1 i).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (∏ i, ((p.2 i).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (∏ i, ((α i).choose (p.1 i) : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.choose_pos (by
      have e : α i = p.1 i + p.2 i := by rw [← hp]; rfl
      omega)).ne'
  push_cast
  rw [← hprod]
  field_simp

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin
open Finset TaylorRingHom

theorem taylor_isRingHom : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A), ∃ T : A →+* MvPowerSeries (Fin n) B, ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f := by
  intro A B _ _ _ n ev ds
  refine ⟨{ toFun := taylor ev (fun i => ⇑(ds i))
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun f => rfl⟩
  · ext α
    rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_one]
    unfold taylor
    rw [iterOp_one]
    split_ifs with h
    · subst h; simp
    · simp
  · intro f g
    ext α
    rw [MvPowerSeries.coeff_mul]
    simp only [MvPowerSeries.coeff_apply]
    unfold taylor
    rw [iterOp_mul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, map_mul, nsmul_eq_mul, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, ← map_natCast (algebraMap ℚ B), ← mul_assoc,
      ← map_mul, factor_identity α p hp, map_mul]
    ring
  · ext α
    rw [MvPowerSeries.coeff_apply, map_zero]
    unfold taylor
    rw [iterOp_zero', map_zero, smul_zero]
  · intro f g
    ext α
    rw [MvPowerSeries.coeff_apply, map_add, MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
    unfold taylor
    rw [iterOp_add, map_add, smul_add]

end GlobalTheory.FormalOrigin
