import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodConstantEqOfCardCmType

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD)

namespace GlobalTheory.JetIntegral

section Size

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [e, map_mul, norm_mul, Real.rpow_add l_pos]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg l_pos.le _)

theorem sz_one : Sz l lam 0 (1 : ℂ) := by
  refine ⟨one_mem _, ?_⟩
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]

theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam ((n : ℝ) * r) (x ^ n) := by
  induction n with
  | zero => simpa using (sz_one (lam := lam))
  | succ n ih =>
    have h := sz_mul ih hx
    rw [pow_succ]
    convert h using 1
    push_cast; ring

theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (sz_one (lam := lam))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sz_inv_l_pow (n : ℕ) : Sz l lam (n : ℝ) (((l : ℂ) ^ n)⁻¹) := by
  have hmem : ((l : ℂ) ^ n)⁻¹ ∈ algebraicClosure ℚ ℂ :=
    inv_mem (pow_mem (natCast_mem _ l) n)
  refine ⟨hmem, ?_⟩
  have e : (⟨((l : ℂ) ^ n)⁻¹, hmem⟩ : algebraicClosure ℚ ℂ) = ((l : algebraicClosure ℚ ℂ) ^ n)⁻¹ := by
    apply Subtype.ext; simp
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  rw [e, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, hl, inv_pow, inv_inv, Real.rpow_natCast]

theorem sz_sign (ε : ℤˣ) : Sz l lam 0 (((ε : ℤ) : ℂ)⁻¹) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using (sz_one (lam := lam))
  · have hmem : (-1 : ℂ) ∈ algebraicClosure ℚ ℂ := neg_mem (one_mem _)
    have e : (⟨-1, hmem⟩ : algebraicClosure ℚ ℂ) = -1 := rfl
    refine ⟨by simpa using hmem, ?_⟩
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, inv_neg, inv_one]
    rw [e, map_neg, map_one, norm_neg, norm_one, Real.rpow_zero]

end Size

theorem expand_id {I : Type} [Fintype I] (D x m C e : ℂ) (a b A : I → ℂ) (κ : I → ℕ) (k : ℕ)
    (hm : m ≠ 0) (he : e ≠ 0) (ha : ∀ i, a i ≠ 0) (hA : ∀ i, A i ≠ 0)
    (h : C ^ k * x = m * D * ∏ i, (e * A i) ^ κ i) :
    D * ∏ i, ((b i / a i) ^ κ i / a i ^ k) = x * m⁻¹ * (C / ∏ i, a i) ^ k * ∏ i, (e⁻¹ * (b i / (a i * A i))) ^ κ i := by
  have h3 : ∏ i, (e⁻¹ * (b i / (a i * A i))) ^ κ i = (∏ i, (b i / a i) ^ κ i) / ∏ i, (e * A i) ^ κ i := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← div_pow]
    congr 1
    field_simp [ha i, hA i, he]
  have h1 : ∏ i, ((b i / a i) ^ κ i / a i ^ k) = (∏ i, (b i / a i) ^ κ i) / ∏ i, a i ^ k := by
    rw [Finset.prod_div_distrib]
  have h2 : (C / ∏ i, a i) ^ k = C ^ k / ∏ i, a i ^ k := by rw [div_pow, Finset.prod_pow]
  have hP2 : ∏ i, a i ^ k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ha i)
  have hP3 : ∏ i, (e * A i) ^ κ i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero he (hA i))
  rw [h1, h2, h3]
  generalize ∏ i, (b i / a i) ^ κ i = P1 at *
  generalize ∏ i, a i ^ k = P2 at *
  generalize ∏ i, (e * A i) ^ κ i = P3 at *
  field_simp
  linear_combination (-P1) * h

end GlobalTheory.JetIntegral

namespace GlobalTheory.JetIntegral

theorem padicVal_nonneg {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (z : ClassGroup (OF E) → ℚ)
    (C : ClassGroup (OF E)) :
    0 ≤ padicValRat l ((l : ℚ) ^ cE_vp l z * (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))) := by
  have hl : (l : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  by_cases hq : z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E) = 0
  · rw [hq, mul_zero, padicValRat.zero]
  rw [padicValRat.mul (pow_ne_zero _ hl) hq, padicValRat.pow, padicValRat.self (Fact.out : l.Prime).one_lt, mul_one]
  have h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z :=
    Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat)
      (Finset.mem_univ C)
  have h2 := Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))
  have h3 : ((-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat : ℤ) ≤ (cE_vp l z : ℤ) := by
    exact_mod_cast h1
  omega

theorem jetInt : EisRule → JetCore → ModelInt → JetInt := by
  intro hEis hJet hMod
  intro E _ _ _ _ I _ d φ s hFD hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ
  classical
  obtain ⟨𝔠, R, hloc, X₀, δ₀, N, T, a, b, hR0, hRq, hAdm, hOver, hab, hC⟩ :=
    hMod E I d φ s hFD hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, fun i => ⟨(hab i).1, (hab i).2.1, (hab i).2.2.2.1, (hab i).2.2.2.2.1⟩, ?_⟩
  intro g κ u hg hu
  obtain ⟨-, -, hUn, -, -, -, hCM, -⟩ := hFD
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  set m : ℂ := (l : ℂ) ^ cE_vp l z with hmdef
  have hm0 : m ≠ 0 := pow_ne_zero _ hl0
  have hmR : m ∈ R := by
    have h := hRq ((l : ℚ) ^ cE_vp l z) (by
      rw [padicValRat.pow, padicValRat.self hl.one_lt]; positivity)
    simpa [hmdef] using h
  have hmz : ∀ C, m * ((z C / 2 ^ Module.finrank ℚ (FR E) : ℚ) : ℂ) ∈ R := by
    intro C
    have h := hRq _ (padicVal_nonneg l z C)
    convert h using 1
    push_cast [hmdef]
    ring
  obtain ⟨r, hr⟩ := hEis E hf2 𝔠 s hs z hz R m hmR hmz
  obtain ⟨ε, hε⟩ := hJet
  obtain ⟨x, hx⟩ := hε E I 𝔠 hf2 R s r hs R X₀ δ₀ N hAdm κ
  have hxe := hx R.subtype (fun a => rfl) φ (condQ 𝔣 Q) y m hCM hc0 (hr I φ (condQ 𝔣 Q) y hCM hc0) T hOver g u hg hu
  have hε0 : ((ε : ℤ) : ℂ) ≠ 0 := by exact_mod_cast ε.ne_zero
  rw [expand_id (iterD u g 0) (R.subtype x) m T.C ((ε : ℤ) : ℂ) a b T.A κ (2 * s) hm0 hε0 (fun i => (hab i).1)
    (fun i => (hab i).2.2.1) hxe]
  have hx0 : Sz l lam 0 (R.subtype x) := hR0 _ x.2
  have hmi : Sz l lam (cE_vp l z : ℝ) m⁻¹ := sz_inv_l_pow _
  have hCp := sz_pow hC (2 * s)
  have hP := sz_prod Finset.univ (fun i => (κ i : ℝ) * (0 + c_vp 𝔣 l)) _
    (fun i _ => sz_pow (sz_mul (sz_sign ε) (hab i).2.2.2.2.2) (κ i))
  have htot := sz_mul (sz_mul (sz_mul hx0 hmi) hCp) hP
  convert htot using 1
  push_cast
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.JetIntegral
