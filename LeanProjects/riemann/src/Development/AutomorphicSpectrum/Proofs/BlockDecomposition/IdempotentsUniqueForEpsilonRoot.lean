import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_eq_of_mul_eq_zero {R I : Type} [CommRing R] [Fintype I] {e e' : I → R}
    (h : CompleteOrthogonalIdempotents e) (h' : CompleteOrthogonalIdempotents e')
    (hz : ∀ c c', c ≠ c' → e c * e' c' = 0) : e = e' := by
  classical
  funext c
  have h1 : e c = e c * e' c := by
    calc e c = e c * ∑ b, e' b := by rw [h'.complete, mul_one]
      _ = e c * e' c := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_single c (fun b _ hb => hz c b hb.symm) (by simp)
  have h2 : e' c = e c * e' c := by
    calc e' c = (∑ b, e b) * e' c := by rw [h.complete, one_mul]
      _ = e c * e' c := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_single c (fun b _ hb => hz b c hb) (by simp)
  rw [h1, ← h2]

theorem one_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n d : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hd : 0 < d) (hdn : d < n) : 1 - ζ ^ d ∣ (n : O) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hd' : (1 - ζ ^ (j + 1)) ∣ ∏ i ∈ Finset.range k, (1 - ζ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem (fun i => 1 - ζ ^ (i + 1)) (Finset.mem_range.2 (by omega))
  rw [h] at hd'
  simpa using hd'

theorem pow_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n a b : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ζ ^ a - ζ ^ b ∣ (n : O) := by
  have hu : ∀ i : ℕ, IsUnit (ζ ^ i) := fun i =>
    (hζ.isUnit (by omega)).pow i
  have key : ∀ {a b : ℕ}, a < b → b < n → ζ ^ a - ζ ^ b ∣ (n : O) := by
    intro a b h1 h2
    have e : ζ ^ a - ζ ^ b = ζ ^ a * (1 - ζ ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    rw [e]
    exact (hu a).mul_left_dvd.2 (one_sub_pow_dvd hζ (by omega) (by omega))
  rcases lt_or_gt_of_ne hab with h | h
  · exact key h hb
  · rw [← neg_sub, neg_dvd]
    exact key h ha

theorem mul_eq_zero_of_pow {O U : Type} [CommRing O] [IsDomain O] [CommRing U] (g : O →+* U)
    {ζ : O} {n a b : ℕ} (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hn : (n : U) ∈ nonZeroDivisors U) {x S S' : U}
    (h : S * (x - g ζ ^ a) = 0) (h' : S' * (x - g ζ ^ b) = 0) : S * S' = 0 := by
  obtain ⟨w, hw⟩ := pow_sub_pow_dvd hζ ha hb hab
  have e : (n : U) = (g ζ ^ a - g ζ ^ b) * g w := by
    rw [← map_natCast g, hw, map_mul, map_sub, map_pow, map_pow]
  have h0 : S * S' * (g ζ ^ a - g ζ ^ b) = 0 := by
    linear_combination S * h' * 1 - S' * h
  have h1 : (S * S') * (n : U) = 0 := by
    rw [e, ← mul_assoc, h0, zero_mul]
  exact (mem_nonZeroDivisors_iff_right.1 hn) _ h1

variable {l : ℕ} [Fact l.Prime]

theorem sharp_s_eq (t : PAlg l) (x : Ob l) :
    t.sharp (t.s x) = t.oC (theta0 l (WittVector.teichmuller l x)) := by
  rw [oC_theta0, sW, WittVector.map_teichmuller]
  rfl

theorem eq_zero_of_sharp (t : PAlg l) {e : t.A} (he : IsIdempotentElem e) (h : t.sharp e = 0) :
    e = 0 :=
  (RL.idem_au t 0 IsIdempotentElem.zero).unique ⟨he, h⟩ ⟨IsIdempotentElem.zero, sharp_zero t⟩

theorem idem_unique : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (m : ℕ) (x : t.U)
    (e e' : ZMod (l ^ m) → t.A),
    CompleteOrthogonalIdempotents e → CompleteOrthogonalIdempotents e' →
    (∀ c, t.sharp (e c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) →
    (∀ c, t.sharp (e' c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) → e = e' := by
  intro l _ ε t m x e e' he he' h h'
  have hζ := (GlobalTheory.T.epsilon_cyclotomic_element_properties ε).2.2.2.2 m
  refine coi_eq_of_mul_eq_zero he he' fun c c' hc => ?_
  have hn : ((l ^ m : ℕ) : t.U) ∈ nonZeroDivisors t.U := by
    rw [Nat.cast_pow]
    exact pow_mem t.l_mem_nzd_U m
  have h1 := h c
  have h2 := h' c'
  rw [sharp_s_eq] at h1 h2
  have h3 := mul_eq_zero_of_pow t.oC hζ (ZMod.val_lt c) (ZMod.val_lt c')
    (fun hv => hc (ZMod.val_injective _ hv)) hn h1 h2
  refine eq_zero_of_sharp t ((he.idem c).mul (he'.idem c')) ?_
  rw [map_mul, h3]

end GlobalTheory.CompanionTheory.ContUniv
