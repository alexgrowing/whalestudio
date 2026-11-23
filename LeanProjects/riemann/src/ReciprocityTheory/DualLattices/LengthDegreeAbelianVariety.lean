import ReciprocityTheory.DualLattices.ColengthSqMulLeProd
import ReciprocityTheory.DualLattices.CokernelsAgreeEquivariantly
import ReciprocityTheory.DualLattices.LengthDegreeOfFrobenius
import ReciprocityTheory.DualLattices.LengthDegreeOfWdetFrobenius

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem lat_conseq (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) (c : NNReal) (hc : c ≤ colen M' M) :
    c ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s :=
  le_trans (by gcongr)
    (colength_sq_mul_le_prod C v R hv hnt n a hinj hint s h A F M M' Mτ M'τ hF hA hM' hMst hMτ hM'τ)

theorem lengthDegree_abelianVariety : PermutedCokernelLowerBoundStatement := permutedCokernelLowerBound_of u6 lenEx killedGen idemGen

theorem av_full (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m))
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hσ : ∀ i, σ (e i) = e (π i))
    (hsT : (∑ i, H.ρ (e i)) + H.P = 1) (hPT : ∀ i, H.ρ (e i) * H.P = 0)
    (hsL : (∑ i, H.ρL (e i)) + H.PL = 1) (hPL : ∀ i, H.ρL (e i) * H.PL = 0)
    (w : Fin m) (hw : π w ≠ w) (d : ℕ)
    (hd : Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))) ≃ₗ[R] (Fin d → R)))
    (hnt : ∃ c : C, 0 < v c ∧ v c < 1) (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a)
    (hint : ∀ τ, v (a τ) ≤ 1) (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C)
    (F : Lat v (Fin n × Fin h)) (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s))
    (hF : F.B = freeMat a h) (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ)
    (Nw : Type) [AddCommGroup Nw] [Module R Nw] (E : htCoker H (e w) (e (π w)) ≃ₗ[R] Nw)
    (cw : NNReal) (hNw : HasLen v R Nw cw) (hcw : cw ≤ colen M' M) :
    ((v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1))) ^ 2 * (v (discr a) : ℝ) ^ h ≤
      ((∏ τ, colen (M'τ τ) (Mτ τ) : NNReal) : ℝ) ^ 2 * (v (discr a) : ℝ) ^ s := by
  obtain ⟨k, c0, ⟨F0⟩, hc0⟩ := hNw
  have hL : HasLen v R (htCoker H (e w) (e (π w))) cw := ⟨k, c0, ⟨E.trans F0⟩, hc0⟩
  have h10 := lengthDegree_abelianVariety
  unfold PermutedCokernelLowerBoundStatement at h10
  have hU := h10 p g C v R O σ cp hS H m e π horth hσ hsT hPT hsL hPL w hw d hd cw hL
  have hlat := lat_conseq C v R hS.integers hnt n a hinj hint s h A F M M' Mτ M'τ hF hA hM'
    hMst hMτ hM'τ cw hcw
  have hlatR : (cw : ℝ) ^ 2 * (v (discr a) : ℝ) ^ h ≤
      ((∏ τ, colen (M'τ τ) (Mτ τ) : NNReal) : ℝ) ^ 2 * (v (discr a) : ℝ) ^ s := by
    exact_mod_cast hlat
  calc _ ≤ (cw : ℝ) ^ 2 * (v (discr a) : ℝ) ^ h := by gcongr
    _ ≤ _ := hlatR

theorem up_full (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (N : Type) [AddCommGroup N] [Module R N]
    (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N) (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ (((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i) ≤ V1 := by
  obtain ⟨k, c0, ⟨F0⟩, hc0⟩ := hN
  have h10 := unramifiedCokernelLowerBound_of hU7 lenEx killedGen idemGen
  unfold UnramifiedCokernelLowerBoundStatement at h10
  exact h10 p g C v R O σ cp hp2 hS H U i V1 ⟨k, c0, ⟨E.trans F0⟩, hc0⟩

private lemma prime_rpow_neg_succ_eq_inv_mul_inv_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (p : ℝ) ^ (-((n : ℝ) + 1)) = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.rpow_neg hp0.le, hn, Real.rpow_natCast, ← inv_pow, pow_succ]
  ring

private lemma prime_inv_lt_one {p : ℕ} [Fact p.Prime] : (p : ℝ)⁻¹ < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 := one_div_lt_one_div_of_lt one_pos hp
  simpa using h1

private lemma summable_prime_rpow_neg_succ {p : ℕ} [Fact p.Prime] :
    Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) := by
  have e : (fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1))) =
      fun n : ℕ => (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := funext fun n => prime_rpow_neg_succ_eq_inv_mul_inv_pow n
  rw [e]
  exact (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one).mul_left _

lemma tsum_geom_p {p : ℕ} [Fact p.Prime] :
    ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) = 1 / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  rw [tsum_congr (fun n : ℕ => prime_rpow_neg_succ_eq_inv_mul_inv_pow (p := p) n), tsum_mul_left,
    tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one]
  field_simp

lemma summable_geom_p {p : ℕ} [Fact p.Prime] (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (B : ℝ)
    (hfB : ∀ n, f n ≤ B) : Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) * f n := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hf0 n))
    (fun n => mul_le_mul_of_nonneg_left (hfB n) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    ((summable_prime_rpow_neg_succ (p := p)).mul_right B)

theorem up_shift (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (ρ r : ℕ) (rG : Fin U.m → ℕ)
    (hrB : ∀ j, U.r j + ρ = rG j) (hrc : (rG (U.cj i) : ℝ) = r - rG i)
    (N : Type) [AddCommGroup N] [Module R N] (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N)
    (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ ((rG i : ℝ) / (p - 1) -
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * rG ((U.φ ^ (n + 1)) i) +
      ((r : ℝ) - rG i - ρ) / (p - 1)) ≤ V1 := by
  have hsplit : ∀ n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (rG ((U.φ ^ (n + 1)) i) : ℝ) =
      (p : ℝ) ^ (-((n : ℝ) + 1)) * (U.r ((U.φ ^ (n + 1)) i) : ℝ) +
        (p : ℝ) ^ (-((n : ℝ) + 1)) * (ρ : ℝ) := by
    intro n
    rw [← hrB]
    push_cast
    ring
  have hs1 : Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) * (U.r ((U.φ ^ (n + 1)) i) : ℝ) :=
    summable_geom_p (fun n : ℕ => (U.r ((U.φ ^ (n + 1)) i) : ℝ)) (fun n => Nat.cast_nonneg _)
      (∑ j, (U.r j : ℝ))
      (fun n => Finset.single_le_sum (f := fun j => (U.r j : ℝ)) (fun j _ => Nat.cast_nonneg _)
        (Finset.mem_univ _))
  have hsum : ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (rG ((U.φ ^ (n + 1)) i) : ℝ) =
      frobSum U i + (ρ : ℝ) / ((p : ℝ) - 1) := by
    rw [tsum_congr hsplit, hs1.tsum_add ((summable_prime_rpow_neg_succ (p := p)).mul_right _), tsum_mul_right,
      tsum_geom_p]
    unfold frobSum
    ring
  have h1 : (rG i : ℝ) = U.r i + ρ := by
    rw [← hrB i]
    push_cast
    ring
  have h2 : (r : ℝ) - rG i - ρ = U.r (U.cj i) := by
    rw [← hrc, ← hrB (U.cj i)]
    push_cast
    ring
  have hexp : (rG i : ℝ) / (p - 1) -
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * rG ((U.φ ^ (n + 1)) i) +
      ((r : ℝ) - rG i - ρ) / (p - 1) =
      ((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i := by
    rw [hsum, h2, h1]
    ring
  rw [hexp]
  exact up_full hU7 p g C v R O σ cp hp2 hS H U i N E V1 hN

end ReciprocityTheory.PGsh.Up
