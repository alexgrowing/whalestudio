import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Mackey
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.RedTopCycM
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.TwistColumnZero
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.NotDvdOfCoprime
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.OrderOfTranslationMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CorestrictionCyclotomicShapiroNormalisedTraceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTraceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L
section Helpers
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cg_mul {A : ValuationSubring Ω} {l n : ℕ} {x y : Ω} (a : Ω) (ha : a ∈ A) (h : CgA A l n x y) :
    CgA A l n (a * x) (a * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨a * z, A.mul_mem _ _ ha hz, by rw [← mul_sub, e]; ring⟩

private theorem cg_trans {A : ValuationSubring Ω} {l n : ℕ} {x y u : Ω} (h : CgA A l n x y) (h' : CgA A l n y u) :
    CgA A l n x u := by
  obtain ⟨z, hz, e⟩ := h
  obtain ⟨z', hz', e'⟩ := h'
  exact ⟨z + z', A.add_mem _ _ hz hz', by rw [mul_add, ← e, ← e']; ring⟩

private theorem lp_mem (A : ValuationSubring Ω) (l k : ℕ) : (l : Ω) ^ k ∈ A := pow_mem (natCast_mem A l) k

private theorem inv_nat_mem {A : ValuationSubring Ω} {l D : ℕ} (hp : l.Prime) (hl : (l : Ω) ∈ A.nonunits) (hD : ¬ l ∣ D) :
    (D : Ω)⁻¹ ∈ A := by
  have hv : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).1 hl
  rcases A.valuation_lt_one_or_eq_one ⟨(D : Ω), natCast_mem A D⟩ with h | h
  · exfalso
    have hg := Nat.gcd_eq_gcd_ab l D
    rw [(hp.coprime_iff_not_dvd.2 hD : Nat.gcd l D = 1)] at hg
    have e : (1 : Ω) = (l : Ω) * ((Nat.gcdA l D : ℤ) : Ω) + (D : Ω) * ((Nat.gcdB l D : ℤ) : Ω) := by
      exact_mod_cast congrArg (Int.cast : ℤ → Ω) hg
    have h1 : A.valuation ((l : Ω) * ((Nat.gcdA l D : ℤ) : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (intCast_mem A _))) hv
    have h2 : A.valuation ((D : Ω) * ((Nat.gcdB l D : ℤ) : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (intCast_mem A _))) h
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [← e, map_one] at h3
    exact lt_irrefl _ h3
  · rw [← A.valuation_le_one_iff, map_inv₀]
    exact le_of_eq (by simpa using congrArg (·⁻¹) h)

private theorem root_mem (A : ValuationSubring Ω) {ζ : Ω} {M : ℕ} (hM : 0 < M) (h : ζ ^ M = 1) : ζ ∈ A := by
  rcases A.mem_or_inv_mem ζ with h1 | h1
  · exact h1
  · have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at h
      exact zero_ne_one h
    have e : ζ = (ζ⁻¹) ^ (M - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      rw [Nat.add_sub_cancel, inv_pow]
      rw [pow_succ] at h
      exact eq_inv_of_mul_eq_one_right h
    rw [e]
    exact pow_mem h1 _

private theorem inZl_mem [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) {A : ValuationSubring Ω} {l k : ℕ} (hp : l.Prime) [NeZero l]
    (hl : (l : Ω) ∈ A.nonunits) {F : Ω} (h : InZl ε l k F) : F ∈ A := by
  obtain ⟨D, hD, hF⟩ := h
  have hz : zt ε l k ∈ A :=
    root_mem A (pow_pos hp.pos k) (IsNTr.isPrimitiveRoot_zt ε l k).pow_eq_one
  have h1 : (D : Ω) * F ∈ A :=
    (Subring.closure_le (t := A.toSubring)).2 (by simpa using hz) hF
  have hD0 : (D : Ω) ≠ 0 := by
    have := algebraRat.charZero Ω
    exact Nat.cast_ne_zero.2 (fun e => hD (e ▸ dvd_zero l))
  have h2 := A.mul_mem _ _ (inv_nat_mem hp hl hD) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2

private theorem inZl_nat_mul {ε : Ω →+* ℂ} {l k : ℕ} {F : Ω} (a : ℕ) (h : InZl ε l k F) : InZl ε l k ((a : Ω) * F) := by
  obtain ⟨D, hD, hF⟩ := h
  refine ⟨D, hD, ?_⟩
  rw [mul_left_comm]
  exact mul_mem (natCast_mem _ a) hF

private theorem exists_chi [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l L : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ u : (ZMod (l ^ L))ˣ, s (zt ε l L) = zt ε l L ^ (u : ZMod (l ^ L)).val := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  have hM : 0 < l ^ L := pow_pos hp.pos L
  haveI : NeZero (l ^ L) := ⟨hM.ne'⟩
  have hz := IsNTr.isPrimitiveRoot_zt ε l L
  have hs : IsPrimitiveRoot (s (zt ε l L)) (l ^ L) := hz.map_of_injective s.injective
  obtain ⟨k, hk, e⟩ := hz.eq_pow_of_pow_eq_one hs.pow_eq_one
  have hc : k.Coprime (l ^ L) := (hz.pow_iff_coprime hM k).1 (e ▸ hs)
  refine ⟨ZMod.unitOfCoprime k hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk, e]

private theorem exists_series (A : ValuationSubring Ω) (f : ℚ → Ω) (hf : ∀ r, f r ∈ A) :
    ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ i : ℕ, g.coeff (i : ℚ) = f i := by
  classical
  have hpwo : (Set.range (Nat.cast : ℕ → ℚ)).IsPWO := by
    rw [← Set.image_univ]
    exact (Set.isPWO_of_wellQuasiOrderedLE _).image_of_monotone Nat.mono_cast
  refine ⟨⟨fun r => if r ∈ Set.range (Nat.cast : ℕ → ℚ) then f r else 0, hpwo.mono fun r hr => ?_⟩, fun r => ?_, fun i => ?_⟩
  · by_contra h
    exact hr (if_neg h)
  · show (if r ∈ Set.range (Nat.cast : ℕ → ℚ) then f r else 0) ∈ A
    split_ifs
    · exact hf r
    · exact A.zero_mem
  · exact if_pos ⟨i, rfl⟩

end Helpers

section Fib

private def redZ (l n m : ℕ) (x : (ZMod (l ^ (m + n)))ˣ) : (ZMod (l ^ m))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_add_right m n)) (ZMod (l ^ m))).toMonoidHom x

private theorem redZ_redTop (l n m N : ℕ) (y : (ZMod (topM l n m (N * N)))ˣ) :
    redZ l n m (redTop l n m N y) = redM l n m (N * N) y := by
  apply Units.ext
  show (ZMod.castHom _ (ZMod (l ^ m))) ((ZMod.castHom _ (ZMod (l ^ (m + n)))) (y : ZMod (topM l n m (N * N)))) =
    (ZMod.castHom _ (ZMod (l ^ m))) (y : ZMod (topM l n m (N * N)))
  exact RingHom.congr_fun (Subsingleton.elim ((ZMod.castHom (pow_dvd_pow l (Nat.le_add_right m n)) (ZMod (l ^ m))).comp
    (ZMod.castHom (Dvd.intro _ rfl : l ^ (m + n) ∣ topM l n m (N * N)) (ZMod (l ^ (m + n)))))
    (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right m n)) (N * N)) (ZMod (l ^ m)))) _

private theorem redZ_coe (l n m : ℕ) [Fact l.Prime] (x : (ZMod (l ^ (m + n)))ˣ) :
    ((redZ l n m x : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = (((x : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m)) := by
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [ZMod.natCast_val]
  rfl

private theorem val_iff (l n m : ℕ) [Fact l.Prime] (x : (ZMod (l ^ (m + n)))ˣ) :
    (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m] ↔ redZ l n m x = 1 := by
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [Units.ext_iff, ← ZMod.natCast_eq_natCast_iff]
  rw [redZ_coe]
  simp

private theorem sum_fib {M : Type*} [AddCommMonoid M] (l n m N : ℕ) [Fact l.Prime] [NeZero (topM l n m (N * N))]
    (f : (ZMod (topM l n m (N * N)))ˣ → M) (zh : (ZMod (l ^ (m + n)))ˣ) (y : (ZMod (l ^ m))ˣ) (hy : redZ l n m zh = y)
    [Fintype (ZMod (l ^ (m + n)))ˣ] [Fintype (ZMod (topM l n m (N * N)))ˣ]
    [DecidablePred fun x : (ZMod (l ^ (m + n)))ˣ => (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]]
    [∀ x, DecidablePred fun y' => redTop l n m N y' = x] [DecidablePred fun y' => redM l n m (N * N) y' = y] :
    ∑ x ∈ Finset.univ.filter (fun x : (ZMod (l ^ (m + n)))ˣ => (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      ∑ y' ∈ Finset.univ.filter (fun y' => redTop l n m N y' = x * zh), f y' =
    ∑ y' ∈ Finset.univ.filter (fun y' => redM l n m (N * N) y' = y), f y' := by
  classical
  have hmul : ∀ a b, redZ l n m (a * b) = redZ l n m a * redZ l n m b := fun a b => map_mul _ a b
  have hinv : ∀ a, redZ l n m a⁻¹ = (redZ l n m a)⁻¹ := fun a => map_inv (Units.map _) a
  have hmaps : ∀ y' ∈ Finset.univ.filter (fun y' => redM l n m (N * N) y' = y),
      redTop l n m N y' * zh⁻¹ ∈ Finset.univ.filter (fun x : (ZMod (l ^ (m + n)))ˣ => (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) := by
    intro y' hy'
    rw [Finset.mem_filter] at hy' ⊢
    refine ⟨Finset.mem_univ _, (val_iff l n m _).2 ?_⟩
    rw [hmul, hinv, redZ_redTop, hy'.2, hy, mul_inv_cancel]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr ?_ fun _ _ => rfl
  ext y'
  have hx1 := (val_iff l n m x).1 (Finset.mem_filter.1 hx).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, by rw [h, mul_inv_cancel_right]⟩
    rw [← redZ_redTop, h, hmul, hx1, one_mul, hy]
  · rintro ⟨-, h⟩
    rw [← h, inv_mul_cancel_right]

end Fib

section Th
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem appr_one (l n : ℕ) [Fact l.Prime] (hn : 1 ≤ n) : (1 : ℤ_[l]).appr n = 1 := by
  have h1 := PadicInt.appr_lt (1 : ℤ_[l]) n
  have h2 := PadicInt.appr_spec n (1 : ℤ_[l])
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, map_natCast, sub_eq_zero] at h2
  have h3 : ((1 : ℕ) : ZMod (l ^ n)) = (((1 : ℤ_[l]).appr n : ℕ) : ZMod (l ^ n)) := by simpa using h2
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  have hgt : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  rw [Nat.mod_eq_of_lt hgt, Nat.mod_eq_of_lt h1] at h3
  exact h3.symm

private theorem thb_sum [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime]
    (n w : ℕ) (hn : 1 ≤ n) (hl : (l : Ω) ∈ A.nonunits) {ι : Type*} (T : Finset ι) (hT : T.Nonempty) (b : ι → X.Fn l)
    (φ : ι → HahnSeries ℚ Ω) (hb : ∀ i, b i ∈ X.B N l w) (h : ∀ i, IsThB X A N l n (b i) (φ i)) :
    IsThB X A N l n (∑ i ∈ T, b i) (∑ i ∈ T, φ i) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a T ha hT ih =>
    have := GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w (b a) (∑ i ∈ T, b i) hl (hb a)
      (Submodule.sum_mem _ fun i _ => hb i) 1 1 (φ a) (∑ i ∈ T, φ i) (h a) ih
    rw [appr_one l n hn] at this
    rw [Finset.sum_cons, Finset.sum_cons]
    simpa using this

private theorem thb_coeff {ε : Ω →+* ℂ} {X : Tower Ω ε} {A : ValuationSubring Ω} {N l n : ℕ} [Fact l.Prime] {b : X.Fn l}
    {φ : HahnSeries ℚ Ω} (h : IsThB X A N l n b φ) (r : ℚ) : φ.coeff r ∈ A := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact h.1 r

private theorem isNT_mul {ε : Ω →+* ℂ} {l L m : ℕ} [NeZero l] {F F' : Ω} (k : ℕ) (h : IsNT ε l L m F F') :
    IsNT ε l L m ((l : Ω) ^ k * F) ((l : Ω) ^ k * F') := by
  obtain ⟨τ, hτ, e⟩ := h
  refine ⟨τ, hτ, ?_⟩
  simp only [map_mul, map_pow, map_natCast]
  rw [← Finset.mul_sum, ← e]
  ring

private theorem exists_kappa (l : ℕ) (hp : l.Prime) (κ : ℚ) : ∃ v : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω), (l : Ω) ∈ A.nonunits → (l : Ω) ^ v * (κ : Ω) ∈ A := by
  obtain ⟨v, b, hb, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd κ.den_nz l hp.ne_one
  refine ⟨v, fun {Ω} _ _ A hl => ?_⟩
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero l))
  have e' : (l : Ω) ^ v * (κ : Ω) = (κ.num : Ω) * (b : Ω)⁻¹ := by
    rw [Rat.cast_def, e]
    push_cast
    field_simp
  rw [e']
  exact A.mul_mem _ _ (intCast_mem A _) (inv_nat_mem hp hl hb)

private theorem small_close {A : ValuationSubring Ω} {l n C L₀ c₂ v c₀ m : ℕ} (hn : n ≤ L₀) {a κ tt T : Ω} (ha : a ∈ A)
    (hT : (l : Ω) ^ c₂ * T ∈ A) (hκ : (l : Ω) ^ v * κ ∈ A) (htt : tt ∈ A) :
    CgA A l n ((l : Ω) ^ (C + (L₀ + c₂ + v)) * a) ((l : Ω) ^ (C + (L₀ + c₂ + v)) * ((l : Ω) ^ c₀ * κ * tt * (l : Ω) ^ m * T)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(l : Ω) ^ C * (l : Ω) ^ q * (l : Ω) ^ c₂ * (l : Ω) ^ v * a -
    (l : Ω) ^ C * (l : Ω) ^ q * (l : Ω) ^ c₀ * ((l : Ω) ^ v * κ) * tt * (l : Ω) ^ m * ((l : Ω) ^ c₂ * T), ?_, ?_⟩
  · refine sub_mem ?_ ?_
    · exact A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (lp_mem A l C) (lp_mem A l q)) (lp_mem A l c₂)) (lp_mem A l v)) ha
    · exact A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (lp_mem A l C) (lp_mem A l q)) (lp_mem A l c₀)) hκ) htt) (lp_mem A l m)) hT
  · simp only [pow_add]
    ring

private theorem final_step {A : ValuationSubring Ω} {l n c cc e c₀ m : ℕ} {a Ψ D F0 T E tt κ : Ω}
    (h0 : CgA A l n a Ψ) (h1 : CgA A l n ((l : Ω) ^ c * ((l : Ω) ^ cc * Ψ)) (D + (l : Ω) ^ c * ((l : Ω) ^ (cc + c₀) * F0 * tt)))
    (hF : F0 = κ * (l : Ω) ^ m * T + (l : Ω) ^ n * E) (hE : E ∈ A) (htt : tt ∈ A) :
    CgA A l n ((l : Ω) ^ (c + cc + e) * a) ((l : Ω) ^ (c + cc + e) * ((l : Ω) ^ c₀ * κ * tt * (l : Ω) ^ m * T) + (l : Ω) ^ e * D) := by
  have s1 := cg_mul ((l : Ω) ^ (c + cc + e)) (lp_mem A l _) h0
  have s2 := cg_mul ((l : Ω) ^ e) (lp_mem A l _) h1
  have s3 : CgA A l n ((l : Ω) ^ e * (D + (l : Ω) ^ c * ((l : Ω) ^ (cc + c₀) * F0 * tt)))
      ((l : Ω) ^ (c + cc + e) * ((l : Ω) ^ c₀ * κ * tt * (l : Ω) ^ m * T) + (l : Ω) ^ e * D) := by
    refine ⟨(l : Ω) ^ e * (l : Ω) ^ c * (l : Ω) ^ (cc + c₀) * E * tt,
      A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (lp_mem A l e) (lp_mem A l c)) (lp_mem A l _)) hE) htt, ?_⟩
    rw [hF]
    simp only [pow_add]
    ring
  have e1 : (l : Ω) ^ (c + cc + e) * Ψ = (l : Ω) ^ e * ((l : Ω) ^ c * ((l : Ω) ^ cc * Ψ)) := by
    simp only [pow_add]; ring
  rw [e1] at s1
  exact cg_trans s1 (cg_trans s2 s3)

end Th
end UpperTheory.Kd.L

theorem UpperTheory.Kd.L.law :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), Odd w → ∃ (c₁ : ℕ) (κ : ℚ), κ ≠ 0 ∧ ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → ∀ y : (ZMod (l ^ m))ˣ, ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ s, Stab A s → (∀ a ∈ A, A.valuation (s a - a) < 1) → s (zt ε l m) = zt ε l m → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y) φ → ∀ tt : ZMod (l ^ n), IsLamG ε l n m s tt → ∀ (β : ℕ) (t a : ℤ), (a : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ i : ℕ, CgA A l n ((l : Ω) ^ c₁ * φ.coeff (i : ℚ)) ((l : Ω) ^ c₁ * ((l : Ω) ^ c₀ * (κ : Ω) * (tt.val : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a * t, 0) (a * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) + (s (g.coeff (i : ℚ)) - g.coeff (i : ℚ))) := by

  intro l _ N _ w hw
  by_cases hl2 : l = 2
  · exact ⟨0, 1, one_ne_zero, fun ε X c d gm P => absurd hl2 P.odd⟩
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  obtain ⟨κ, hκ, L₀, har⟩ := arith l N w hw.pos
  obtain ⟨c₂, hsm⟩ := small l w L₀
  obtain ⟨cc, hmk⟩ := mackey l
  obtain ⟨c, hcor⟩ := GlobalTheory.T.corestriction_cyclotomic_shapiro_normalisedTrace l hl2
  obtain ⟨v, hv⟩ := exists_kappa l hp κ
  refine ⟨c + cc + (L₀ + c₂ + v), κ, hκ, ?_⟩
  intro Ω _ _ _ _ ε X c' d gm P A hl x m n c₀ hm hmn bB hbB y
  by_cases hsmall : m + n < L₀
  · refine ⟨0, fun r => by simp, ?_⟩
    intro s hs hres hz φ hφ tt htt β t a ha hβ hβ1 ht i
    simp only [HahnSeries.coeff_zero, map_zero, sub_self, add_zero]
    exact small_close (C := c + cc) (by omega) (thb_coeff hφ _)
      (hsm ε N c' d gm P A hl x m hm (by omega) β t a i) (hv A hl) (natCast_mem A _)
  have hL : L₀ ≤ m + n := not_lt.1 hsmall
  have hn : 1 ≤ n := hm.trans hmn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hj := X.j_hol
  obtain ⟨hB, hcoc⟩ := zcoc ε X l N c' d gm P A hl x w m n c₀ hw hm bB hbB
  choose Φ hΦ using fun s z => GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l halg hj hl2 P.cop P.five hl n w hw (bMid X l n m N bB s z) (hB s z)
  choose χ hχ using fun s => exists_chi ε l (m + n) s
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨zh, hzh⟩ : ∃ zh, redZ l n m zh = y := ZMod.unitsMap_surjective (pow_dvd_pow l (Nat.le_add_right m n)) y
  have hdv : N * l ∣ topMu l n m N := by
    refine ⟨l ^ (m + n - 1) * N, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, m + n = k + 1 := ⟨m + n - 1, by omega⟩
    simp only [topMu, hk, Nat.add_sub_cancel, pow_succ]
    ring
  obtain ⟨R, hR⟩ := (reps l N c' d gm P (topMu l n m N) hdv).1
  obtain ⟨hFs, hFa⟩ := har ε c' d gm P x m n hm R hR zh
  obtain ⟨ξ, hξA, hξ⟩ := hmk ε X N c' d gm P A hl x w m n c₀ hw hm hn bB hbB R hR zh
  choose F0 hF0 using fun r => GlobalTheory.T.exists_unique_normalizedCyclotomicTrace ε l (m + n) m hm (by omega) (Fsum ε l n m N x c' d w gm R zh r) (hFs r)
  obtain ⟨ξ', hξ'A, hξ'⟩ := hcor ε A hl (m + n) n m hm hmn (by omega) χ hχ
    (fun s u r => (l : Ω) ^ cc * (Φ s (u * zh)).coeff r)
    (fun s u r => A.mul_mem _ _ (lp_mem A l cc) (thb_coeff (hΦ s _).1 r))
    (fun s t hs ht u r => by
      have h := hcoc χ hχ s t hs (u * zh) _ _ _ (hΦ (s * t) _).1 (hΦ s _).1 (hΦ t (u * zh * (χ s)⁻¹)).1 r
      have h' := cg_mul ((l : Ω) ^ cc) (lp_mem A l cc) h
      rw [mul_add] at h'
      simp only [map_mul, map_pow, map_natCast]
      rwa [show u * (χ s)⁻¹ * zh = u * zh * (χ s)⁻¹ from mul_right_comm _ _ _])
    ξ (fun r => (l : Ω) ^ (cc + c₀) * Fsum ε l n m N x c' d w gm R zh r)
    (fun r => ⟨hξA r, by simpa using inZl_nat_mul (l ^ (cc + c₀)) (hFs r)⟩)
    (fun s hs hres h1 tt htt r => by
      have hz : s (zt ε l (m + n)) = zt ε l (m + n) := by
        have hgt : 1 < l ^ (m + n) := Nat.one_lt_pow (by omega) hp.one_lt
        rw [hχ s, h1, Units.val_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hgt, pow_one]
      have h := hξ s hs hres hz tt htt _ (hΦ s zh).1 r
      rw [one_mul]
      have e : (l : Ω) ^ (cc + c₀) * Fsum ε l n m N x c' d w gm R zh r * (tt.val : Ω) =
          (l : Ω) ^ cc * ((l : Ω) ^ c₀ * Fsum ε l n m N x c' d w gm R zh r * (tt.val : Ω)) := by
        rw [pow_add]; ring
      rwa [e])
    (fun r => (l : Ω) ^ (cc + c₀) * F0 r) (fun r => isNT_mul _ (hF0 r).1)
  obtain ⟨g, hgA, hg⟩ := exists_series A (fun r => (l : Ω) ^ (L₀ + c₂ + v) * ξ' r)
    (fun r => A.mul_mem _ _ (lp_mem A l _) (hξ'A r))
  refine ⟨g, hgA, ?_⟩
  intro s hs hres hzm φ hφ tt htt β t a ha hβ hβ1 ht i
  have hone : (1 : (ZMod (l ^ (m + n)))ˣ) ∈ Finset.univ.filter
      (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (val_iff l n m 1).2 (map_one (Units.map _))⟩
  have hthb := thb_sum X A N l n w hn hl _ ⟨1, hone⟩ (fun u => bMid X l n m N bB s (u * zh))
    (fun u => Φ s (u * zh)) (fun u => hB s _) (fun u => (hΦ s _).1)
  have hpush : ∑ u ∈ Finset.univ.filter (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      bMid X l n m N bB s (u * zh) = GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y := by
    simp only [bMid, GlobalTheory.KA.push]
    exact sum_fib l n m N (bTop X l n m N bB s) zh y hzh
  rw [hpush] at hthb
  have hmem : GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y ∈ X.B N l w := by
    rw [← hpush]
    exact Submodule.sum_mem _ fun u _ => hB s _
  have h0 := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l hj hl2 P.cop P.five hl n w hw _ hmem φ _ hφ hthb (i : ℚ)
  have hβ' : β ≡ (zh : ZMod (l ^ (m + n))).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, hβ, ← redZ_coe, hzh]
  obtain ⟨E, hE, hFE⟩ := hFa hL i (F0 i) (hF0 i).1 β t a ha hβ' hβ1 ht
  have h1 := hξ' s hs hres hzm tt htt (i : ℚ)
  simp only [← Finset.mul_sum] at h1
  have hΨ : (∑ u ∈ Finset.univ.filter (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      Φ s (u * zh)).coeff (i : ℚ) = ∑ u ∈ Finset.univ.filter (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      (Φ s (u * zh)).coeff (i : ℚ) := HahnSeries.coeff_sum _
  rw [← hΨ] at h1
  have hfin := final_step (e := L₀ + c₂ + v) (c₀ := c₀) h0 h1 hFE (inZl_mem ε hp hl hE) (natCast_mem A tt.val)
  have eg : s (g.coeff (i : ℚ)) - g.coeff (i : ℚ) = (l : Ω) ^ (L₀ + c₂ + v) * (s (ξ' (i : ℚ)) - ξ' (i : ℚ)) := by
    rw [hg i, map_mul, map_pow, map_natCast, mul_sub]
  rw [eg]
  exact hfin
