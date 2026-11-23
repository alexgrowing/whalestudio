import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import GroundTheory.PAdicHodge.ACrisBdRGalois

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCris

section Abstract

theorem eq_of_factorial_mul {B : Type} [CommRing B] [Algebra ℚ B] {l : ℕ} (hl : l ≠ 0) (M n : ℕ)
    {D b : B} (h : (n.factorial : B) * D = b ^ n) :
    D = (l : B) ^ (M * n) * (((n.factorial : ℚ))⁻¹ • (((l : ℚ) ^ M)⁻¹ • b) ^ n) := by
  have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [smul_pow, ← h, Algebra.smul_def, Algebra.smul_def]
  have e1 : (l : B) = algebraMap ℚ B (l : ℚ) := (map_natCast _ _).symm
  have e2 : (n.factorial : B) = algebraMap ℚ B (n.factorial : ℚ) := (map_natCast _ _).symm
  rw [e1, e2, ← map_pow, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul]
  have e3 : (l : ℚ) ^ (M * n) * (n.factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ n * (n.factorial : ℚ) = 1 := by
    rw [pow_mul, inv_pow]
    have : ((l : ℚ) ^ M) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl')
    field_simp
  rw [e3, map_one, one_mul]

variable {W A B C : Type} [CommRing W] [CommRing A] [Algebra W A] [CommRing B] [Algebra ℚ B]
  [CommRing C] [Algebra ℚ C]

theorem map_dp_mem (T : A →+* B) (g : B →+* C) (f : W →+* C)
    (hf : ∀ w, g (T (algebraMap W A w)) = f w) (ξ : W) {l : ℕ} (hl : l ≠ 0) (M n : ℕ) {d : A}
    (hd : (n.factorial : A) * d = algebraMap W A ξ ^ n) : g (T d) ∈ sub f ξ l M := by
  have h1 : (n.factorial : B) * T d = T (algebraMap W A ξ) ^ n := by
    rw [← map_pow, ← hd, map_mul, map_natCast]
  have h2 : g (T d) = (l : C) ^ (M * n) * dpE f ξ l M n := by
    rw [eq_of_factorial_mul hl M n h1, map_mul, map_pow, map_natCast, dpE, η, map_rat_smul, map_pow,
      map_rat_smul, hf]
  rw [h2]
  exact mul_mem (pow_mem (natCast_mem _ l) _) (Subring.subset_closure (Or.inr ⟨n, rfl⟩))

theorem map_adjoin_mem (T : A →+* B) (g : B →+* C) (f : W →+* C)
    (hf : ∀ w, g (T (algebraMap W A w)) = f w) (ξ : W) {l : ℕ} (hl : l ≠ 0) (M : ℕ) (d : ℕ → A)
    (hd : ∀ n, (n.factorial : A) * d n = algebraMap W A ξ ^ n) {s : A}
    (hs : s ∈ Algebra.adjoin W (Set.range d)) : g (T s) ∈ sub f ξ l M := by
  induction hs using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    exact map_dp_mem T g f hf ξ hl M n (hd n)
  | algebraMap x => rw [hf]; exact Subring.subset_closure (Or.inl (Set.mem_range_self x))
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

end Abstract

variable (l : ℕ) [Fact l.Prime]

local notation "𝔸" => Localization.Away (l : AInf ℂ_[l] l)

theorem mem_adjoin_dpow {s : 𝔸} (hs : s ∈ ACris.ACrisZero ℂ_[l] l) :
    s ∈ Algebra.adjoin (AInf ℂ_[l] l) (Set.range fun n : ℕ => ACris.dpow n (xi0 l)) := by
  rw [← ACris.acrisZero_eq_adjoin ker_theta0]; exact hs

theorem factorial_mul_dpow_xi (n : ℕ) :
    ((n.factorial : 𝔸)) * ACris.dpow n (xi0 l) = algebraMap (AInf ℂ_[l] l) 𝔸 (xi0 l) ^ n :=
  ACris.factorial_mul_dpow n _

theorem pk_toB_algebraMap (k : ℕ) (w : AInf ℂ_[l] l) :
    pk l k (toBDeRhamPlus (normInteger ℂ_[l]) l (algebraMap (AInf ℂ_[l] l) 𝔸 w)) = fk l k w := rfl

set_option maxHeartbeats 400000 in
theorem pk_toB_mem (k M : ℕ) {s : 𝔸} (hs : s ∈ ACris.ACrisZero ℂ_[l] l) :
    pk l k (toBDeRhamPlus (normInteger ℂ_[l]) l s) ∈ sub (fk l k) (xi0 l) l M :=
  map_adjoin_mem (W := AInf ℂ_[l] l) (A := 𝔸) (B := BdRp l) (C := Bk l k)
    (toBDeRhamPlus (normInteger ℂ_[l]) l) (pk l k) (fk l k) (pk_toB_algebraMap l k) (xi0 l)
    (Fact.out : l.Prime).ne_zero M (fun n => ACris.dpow n (xi0 l))
    (factorial_mul_dpow_xi l) (mem_adjoin_dpow l hs)

set_option maxHeartbeats 800000 in

theorem cris_in (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l) :
    Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  obtain ⟨s, hs, hst⟩ := (ACris.embedding₂ ℂ_[l] l k c).2
  have e1 : IsPerfectoidField.evalB ℂ_[l] l k (ACris.iota ℂ_[l] l c) =
      (ACris.embedding₂ ℂ_[l] l k c).1 := ACris.evalₐ_iota k c
  have e2 := IsPerfectoidField.evalB_toBDeRhamPlus (K := ℂ_[l]) (p := l) k s
  have e3 : ACris.iota ℂ_[l] l c - toBDeRhamPlus (normInteger ℂ_[l]) l s ∈
      Ideal.span {tBdR l ^ k} := by
    rw [← Ideal.span_singleton_pow, ← maximalIdeal_eq_span_tBdR, ← IsPerfectoidField.ker_evalB,
      RingHom.mem_ker, map_sub, e1, e2, sub_eq_zero]
    exact hst.symm
  have e4 : pk l k (ACris.iota ℂ_[l] l c) = pk l k (toBDeRhamPlus (normInteger ℂ_[l]) l s) :=
    Ideal.Quotient.eq.2 e3
  rw [e4]
  exact pk_toB_mem l k M hs

end GlobalTheory.CompanionTheory.LatCris
