import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribedStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.AlmostEt

section DerLemmas

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem IsDerOn.mono' {B C : Subalgebra A S} {D : S → M} (h : IsDerOn C D) (hBC : B ≤ C) :
    IsDerOn B D :=
  ⟨fun x hx y hy => h.add x (hBC hx) y (hBC hy), fun x hx y hy => h.mul x (hBC hx) y (hBC hy), h.alg⟩

theorem IsDerOn.pow_succ_der {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    (k : ℕ) : D (x ^ (k + 1)) = (((k + 1 : ℕ) : S) * x ^ k) • D x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ' x (k + 1), h.mul x hx _ (pow_mem hx _), ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem IsDerOn.eq_on_adjoin {s : Set S} {D₁ D₂ : S → M} (h₁ : IsDerOn (Algebra.adjoin A s) D₁)
    (h₂ : IsDerOn (Algebra.adjoin A s) D₂) (hs : ∀ x ∈ s, D₁ x = D₂ x) :
    ∀ x ∈ Algebra.adjoin A s, D₁ x = D₂ x := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap a => rw [h₁.alg, h₂.alg]
  | add x y hx hy ihx ihy => rw [h₁.add x hx y hy, h₂.add x hx y hy, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [h₁.mul x hx y hy, h₂.mul x hx y hy, ihx, ihy]

end DerLemmas

section TowerDer

open GlobalTheory.K5 Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow_p (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.ζpow m)

theorem qS_succ_pow_p (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.qpow m)

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert (zS T m) {qS T m})

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton (qS T m)))

theorem zS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T (m + 1) := by
  rw [← zS_succ_pow_p]; exact pow_mem (zS_mem_levelAlg T (m + 1)) _

theorem qS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T (m + 1) := by
  rw [← qS_succ_pow_p]; exact pow_mem (qS_mem_levelAlg T (m + 1)) _

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) :=
  Algebra.adjoin_le (Set.insert_subset_iff.2 ⟨zS_mem_levelAlg_succ T m,
    Set.singleton_subset_iff.2 (qS_mem_levelAlg_succ T m)⟩)

theorem frac_smul_mk (s : integralClosure (O0 p) Ω) (x : Ω) :
    s • (Submodule.Quotient.mk x : Frac p Ω) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero (s : integralClosure (O0 p) Ω) :
    (Submodule.Quotient.mk (s : Ω) : Frac p Ω) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_relation (hc : CharZero Ω) (T : Tower p Ω) (m : ℕ) :
    (Polynomial.aeval (zS T (m + 1)) (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))) •
      (Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) : Frac p Ω) = 0 := by
  set z := zS T (m + 1)
  set ζ := T.ζ (m + 1)
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  have hξ : IsPrimitiveRoot (ζ ^ p ^ m) p := by
    have := (T.prim (m + 1)).pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this

  set gS : integralClosure (O0 p) Ω := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (ζ ^ p ^ m) ^ j := by
    simp [gS, z, ζ, zS]
  have hg : (gS : Ω) * (ζ ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp

  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (T.prim (m + 1)).isRoot_cyclotomic hpos
  have hid := congrArg (fun f => Polynomial.aeval ζ (Polynomial.derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add, map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  have hzval : (Polynomial.aeval z (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) : Ω)
      = Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) := by
    exact (Polynomial.aeval_algHom_apply (integralClosure (O0 p) Ω).val z _).symm
  rw [frac_smul_mk, hzval]
  set F := Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))
  have hζ1 : ζ ^ p ^ (m + 1) = 1 := (T.prim (m + 1)).pow_eq_one
  have hF : F * (ζ ^ p ^ m - 1) * ζ = (p : Ω) ^ (m + 1) := by
    have h2 : F * (ζ ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * ζ ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    rw [h2, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : ζ ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : F * (ζ * p / (p : Ω) ^ (m + 1)) = ((-gS : integralClosure (O0 p) Ω) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

end TowerDer

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

open GlobalTheory.K5

theorem IsDerOn.pow_der {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B) {n : ℕ}
    (hn : 0 < n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using h.pow_succ_der hx k

theorem zeta_derivation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
        D (qS T m) = 0 := by
  intro p hp Ω _ _ hc T
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hlev : ∀ m : ℕ, ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (levelAlg T (m + 1)) D ∧
        D (zS T (m + 1)) = Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) ∧
        D (qS T (m + 1)) = 0 := fun m =>
    GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hc T (m + 1) (Nat.succ_pos m) (Frac p Ω) _ 0
      (cyc_relation inferInstance T m) (smul_zero _)
  choose D hD hDz hDq using hlev
  have hval : ∀ m, D m (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
      D m (qS T m) = 0 := by
    intro m
    constructor
    · rw [← zS_succ_pow_p, (hD m).pow_der (zS_mem_levelAlg T (m + 1)) hp.out.pos, hDz m, frac_smul_mk]
      congr 1
      have hc1 : ((zS T (m + 1) : integralClosure (O0 p) Ω) : Ω) = T.ζ (m + 1) := rfl
      push_cast
      rw [hc1, ← T.ζpow m, ← pow_sub_one_mul hp.out.ne_zero (T.ζ (m + 1))]
      field_simp
      ring
    · rw [← qS_succ_pow_p, (hD m).pow_der (qS_mem_levelAlg T (m + 1)) hp.out.pos, hDq m, smul_zero]
  have hcompat : ∀ m, ∀ x ∈ levelAlg T (m + 1), D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zS T (m + 1), qS T (m + 1)})
      ((hD (m + 1)).mono' (levelAlg_le_succ T (m + 1))) (hD m) ?_
    rintro x (rfl | hx)
    · rw [(hval (m + 1)).1, hDz m]
    · rw [Set.mem_singleton_iff.1 hx, (hval (m + 1)).2, hDq m]
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono D hD hcompat
  have hle : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (zS_mem_levelAlg_succ T m)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (qS_mem_levelAlg_succ T m)
  refine ⟨D', hD'.mono' hle, fun m => ⟨?_, ?_⟩⟩
  · rw [hD'eq m _ (zS_mem_levelAlg_succ T m), (hval m).1]
  · rw [hD'eq m _ (qS_mem_levelAlg_succ T m), (hval m).2]

end GlobalTheory.AlmostEt
