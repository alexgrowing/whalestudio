import Mathlib
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne

noncomputable section

namespace GlobalTheory.SubringSeries

open MvPowerSeries Formalism.FG.InjVAux

variable {K : Type} [Field K] {κ : Type}

def intS (A : Subring K) (κ : Type) : Subring (MvPowerSeries κ K) where
  carrier := {F | ∀ n, coeff n F ∈ A}
  mul_mem' := by
    classical
    intro a b ha hb n
    rw [coeff_mul]
    exact A.sum_mem fun x _ => A.mul_mem (ha _) (hb _)
  one_mem' := by
    classical
    intro n
    rw [coeff_one]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  add_mem' := fun ha hb n => by rw [map_add]; exact A.add_mem (ha n) (hb n)
  zero_mem' := fun n => by rw [map_zero]; exact A.zero_mem
  neg_mem' := fun ha n => by rw [map_neg]; exact A.neg_mem (ha n)

variable {A : Subring K}

theorem mem_intS {F : MvPowerSeries κ K} : F ∈ intS A κ ↔ ∀ n, coeff n F ∈ A := Iff.rfl

theorem C_mem {a : K} (ha : a ∈ A) : (C a : MvPowerSeries κ K) ∈ intS A κ := by
  classical
  intro n
  rw [coeff_C]
  split_ifs
  exacts [ha, A.zero_mem]

theorem X_mem (k : κ) : (X k : MvPowerSeries κ K) ∈ intS A κ := by
  classical
  intro n
  rw [coeff_X]
  split_ifs
  exacts [A.one_mem, A.zero_mem]

theorem finsum_mem' {ι : Type} {f : ι → K} (h : ∀ i, f i ∈ A) : ∑ᶠ i, f i ∈ A :=
  finsum_induction (fun x => x ∈ A) A.zero_mem (fun _ _ => A.add_mem) h

theorem subst_sub_mem {ι : Type} {a b : ι → MvPowerSeries κ K} (ha : HasSubst a) (hb : HasSubst b)
    (E : MvPowerSeries ι K) (c : K)
    (h : ∀ d : ι →₀ ℕ, C (c * coeff d E) * ((d.prod fun s e => a s ^ e) - d.prod fun s e => b s ^ e) ∈ intS A κ) :
    C c * (subst a E - subst b E) ∈ intS A κ := by
  intro n
  rw [coeff_C_mul, map_sub, coeff_subst ha, coeff_subst hb,
    ← finsum_sub_distrib (coeff_subst_finite ha E n) (coeff_subst_finite hb E n), mul_finsum]
  refine finsum_mem' fun d => ?_
  have := h d n
  rw [coeff_C_mul, map_sub] at this
  simpa [mul_sub, mul_assoc] using this

theorem psubst_sub_mem {a b : MvPowerSeries κ K} (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (f : PowerSeries K) (c : K)
    (h : ∀ d : ℕ, C (c * PowerSeries.coeff d f) * (a ^ d - b ^ d) ∈ intS A κ) :
    C c * (f.subst a - f.subst b) ∈ intS A κ := by
  intro n
  rw [coeff_C_mul, map_sub, PowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite ha f n) (PowerSeries.coeff_subst_finite hb f n), mul_finsum]
  refine finsum_mem' fun d => ?_
  have := h d n
  rw [coeff_C_mul, map_sub] at this
  simpa [mul_sub, mul_assoc] using this

theorem subst_mem {ι : Type} {a : ι → MvPowerSeries κ K} (ha : HasSubst a) (hA : ∀ i, a i ∈ intS A κ)
    {E : MvPowerSeries ι K} (hE : E ∈ intS A ι) : subst a E ∈ intS A κ := by
  intro n
  rw [coeff_subst ha]
  refine finsum_mem' fun d => ?_
  rw [smul_eq_mul]
  refine A.mul_mem (hE d) (((intS A κ).prod_mem fun i _ => (intS A κ).pow_mem (hA i) _) n)

theorem psubst_mem {a : MvPowerSeries κ K} (ha : PowerSeries.HasSubst a) (hA : a ∈ intS A κ)
    {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ A) : f.subst a ∈ intS A κ := by
  intro n
  rw [PowerSeries.coeff_subst ha]
  refine finsum_mem' fun d => ?_
  rw [smul_eq_mul]
  exact A.mul_mem (hf d) (((intS A κ).pow_mem hA _) n)

theorem pow_congr {R : Type} [CommRing R] (S : Subring R) (p : ℕ) {P Q y : R} (hQ : Q ∈ S) (hy : y ∈ S)
    (h : P = Q + p * y) {k n : ℕ} (hn : p ^ k ∣ n) : ∃ z ∈ S, P ^ n - Q ^ n = (p : R) ^ (k + 1) * z := by
  obtain ⟨m, rfl⟩ := hn
  have hP : P ∈ S := h ▸ S.add_mem hQ (S.mul_mem (natCast_mem S p) hy)
  have h1 : ((p : ℕ) : S) ∣ (⟨P, hP⟩ : S) - ⟨Q, hQ⟩ := ⟨⟨y, hy⟩, Subtype.ext (by simp [h])⟩
  have h2 := (dvd_sub_pow_of_dvd_sub h1 k).trans (sub_dvd_pow_sub_pow _ _ m)
  obtain ⟨z, hz⟩ := h2
  refine ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simpa [pow_mul] using this

def frob (p : ℕ) (hp : p ≠ 0) (σ : K →+* K) (κ : Type) : MvPowerSeries κ K →+* MvPowerSeries κ K :=
  (expand p hp : MvPowerSeries κ K →ₐ[K] MvPowerSeries κ K).toRingHom.comp (map σ)

section Frob

variable {p : ℕ} {hp : p ≠ 0} {σ : K →+* K}

theorem frob_apply (F : MvPowerSeries κ K) : frob p hp σ κ F = expand p hp (map σ F) := rfl

theorem frob_C (a : K) : frob p hp σ κ (C a) = C (σ a) := by
  rw [frob_apply, map_C, expand_C]

theorem frob_X (k : κ) : frob p hp σ κ (X k) = X k ^ p := by
  rw [frob_apply, map_X, expand_X]

theorem constantCoeff_frob {F : MvPowerSeries κ K} (h : constantCoeff F = 0) :
    constantCoeff (frob p hp σ κ F) = 0 := by
  rw [frob_apply, constantCoeff_expand, constantCoeff_map, h, map_zero]

theorem frob_subst {ι : Type} [Finite ι] {a : ι → MvPowerSeries κ K} (ha : ∀ i, constantCoeff (a i) = 0)
    (E : MvPowerSeries ι K) :
    frob p hp σ κ (subst a E) = subst (fun i => frob p hp σ κ (a i)) (map σ E) := by
  rw [frob_apply, map_subst (hasSubst_of_constantCoeff_zero ha), expand_subst]
  · rfl
  · exact hasSubst_of_constantCoeff_zero fun i => by rw [constantCoeff_map, ha, map_zero]

theorem frob_psubst {a : MvPowerSeries κ K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    frob p hp σ κ (f.subst a) = (PowerSeries.map σ f).subst (frob p hp σ κ a) :=
  frob_subst (ι := Unit) (a := fun _ => a) (fun _ => ha) f

theorem coeff_frob_cases (F : MvPowerSeries κ K) (n : κ →₀ ℕ) :
    coeff n (frob p hp σ κ F) = 0 ∨ ∃ m, p • m = n ∧ coeff n (frob p hp σ κ F) = σ (coeff m F) := by
  by_cases hd : ∀ i, p ∣ n i
  · obtain ⟨m, hm⟩ : ∃ m : κ →₀ ℕ, p • m = n := ⟨n.mapRange (fun a => a / p) (by simp),
      by ext i; simp [Nat.mul_div_cancel' (hd i)]⟩
    exact Or.inr ⟨m, hm, by rw [← hm, frob_apply, coeff_expand_smul, coeff_map]⟩
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    exact Or.inl (by rw [frob_apply, coeff_expand_of_not_dvd p hp _ hi])

theorem hasOrd_frob (h2 : 2 ≤ p) {F : MvPowerSeries κ K} {N : ℕ} (hN : 1 ≤ N) (h : HasOrd N F) :
    HasOrd (N + 1) (frob p hp σ κ F) := by
  intro n hn
  rcases coeff_frob_cases (hp := hp) (σ := σ) F n with h0 | ⟨m, hm, h1⟩
  · exact h0
  · rw [h1, h m, map_zero]
    rw [← hm, map_nsmul, smul_eq_mul] at hn
    nlinarith

theorem frob_congr [Fact p.Prime] (hu : ¬ IsUnit (p : A)) (hσ : ∀ x ∈ A, ∃ y ∈ A, σ x = x ^ p + p * y)
    {P : MvPowerSeries κ K} (hP : P ∈ intS A κ) :
    ∃ y ∈ intS A κ, frob p hp σ κ P = P ^ p + p * y := by
  have hσA : ∀ x ∈ A, σ x ∈ A := fun x hx => by
    obtain ⟨y, hy, h⟩ := hσ x hx
    exact h ▸ A.add_mem (A.pow_mem hx _) (A.mul_mem (natCast_mem A p) hy)
  let I : Ideal A := Ideal.span {(p : A)}
  haveI : CharP (A ⧸ I) p := CharP.quotient A p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (A ⧸ I) p := ExpChar.prime Fact.out
  let s : A →+* A := σ.restrict A A hσA
  let P0 : MvPowerSeries κ A := fun n => ⟨coeff n P, hP n⟩
  have hP0 : map A.subtype P0 = P := by ext n; rfl
  have hs : (Ideal.Quotient.mk I).comp s = (frobenius (A ⧸ I) p).comp (Ideal.Quotient.mk I) := by
    ext x
    obtain ⟨y, hy, h⟩ := hσ x x.2
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨⟨y, hy⟩, Subtype.ext (by simp [s, h])⟩
  have key : map (Ideal.Quotient.mk I) (expand p hp (map s P0) - P0 ^ p) = 0 := by
    rw [map_sub, map_pow, map_expand, ← map_frobenius_expand p hp, map_expand, sub_eq_zero]
    congr 1
    ext n
    simpa using RingHom.congr_fun hs (coeff n P0)
  have hd : ∀ n, ∃ z : A, coeff n (expand p hp (map s P0) - P0 ^ p) = p * z := fun n => by
    have := congrArg (coeff n) key
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose z hz using hd
  obtain ⟨Z, hZ⟩ : ∃ Z : MvPowerSeries κ K, ∀ n, coeff n Z = z n := ⟨fun n => (z n : K), fun _ => rfl⟩
  refine ⟨Z, fun n => hZ n ▸ (z n).2, ?_⟩
  have e : frob p hp σ κ P - P ^ p = map A.subtype (expand p hp (map s P0) - P0 ^ p) := by
    rw [map_sub, map_pow, map_expand, hP0, frob_apply, ← hP0]
    rfl
  rw [← sub_eq_iff_eq_add', e]
  ext n
  rw [coeff_map, hz, ← map_natCast (C : K →+* MvPowerSeries κ K), coeff_C_mul, hZ]
  simp

end Frob

theorem hasOrd_subst_sub {f : PowerSeries K} (h1 : PowerSeries.coeff 1 f = 1) {a b : MvPowerSeries κ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {N : ℕ} (h : HasOrd (N + 1) (a - b)) :
    HasOrd (N + 2) (f.subst a - f.subst b - (a - b)) := by
  have haS := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hbS := PowerSeries.HasSubst.of_constantCoeff_zero hb
  have hg : Good N 1 a b := ⟨hasOrd_one_of_cc ha, hasOrd_one_of_cc hb, h⟩
  intro n hn
  rw [map_sub, map_sub, PowerSeries.coeff_subst haS, PowerSeries.coeff_subst hbS,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite haS f n) (PowerSeries.coeff_subst_finite hbS f n),
    finsum_eq_single _ 1]
  · simp [h1]
  · intro e he
    rw [← smul_sub, ← map_sub]
    rcases Nat.eq_zero_or_pos e with rfl | h0
    · simp
    · rw [(hg.pow e).2.2 n (by omega), smul_zero]

theorem mem_of_subst_mem {f : PowerSeries K} (h1 : PowerSeries.coeff 1 f = 1)
    (T : AddSubgroup (MvPowerSeries κ K))
    (hT : ∀ P ∈ intS A κ, constantCoeff P = 0 → f.subst P ∈ T)
    (hlow : ∀ D ∈ T, ∀ N, HasOrd (N + 1) D → ∀ n : κ →₀ ℕ, n.degree = N + 1 → coeff n D ∈ A)
    {t : MvPowerSeries κ K} (ht : constantCoeff t = 0) (hf : f.subst t ∈ T) : t ∈ intS A κ := by
  have main : ∀ N, ∀ n : κ →₀ ℕ, n.degree < N + 1 → coeff n t ∈ A := by
    intro N
    induction N with
    | zero => intro n hn; rw [hasOrd_one_of_cc ht n hn]; exact A.zero_mem
    | succ N ih =>
      intro n hn
      rcases (Nat.lt_succ_iff_lt_or_eq.1 hn) with hlt | heq
      · exact ih n hlt
      obtain ⟨P, hP⟩ : ∃ P : MvPowerSeries κ K, ∀ m, coeff m P = if m.degree < N + 1 then coeff m t else 0 :=
        ⟨fun m => if m.degree < N + 1 then coeff m t else 0, fun _ => rfl⟩
      have hPA : P ∈ intS A κ := fun m => by
        rw [hP]; split_ifs with h
        exacts [ih m h, A.zero_mem]
      have hP0 : constantCoeff P = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, hP, coeff_zero_eq_constantCoeff_apply, ht, ite_self]
      have ho : HasOrd (N + 1) (t - P) := fun m hm => by rw [map_sub, hP, if_pos hm, sub_self]
      have h2 := hasOrd_subst_sub h1 ht hP0 ho
      have h3 : HasOrd (N + 1) (f.subst t - f.subst P) := by
        have := (h2.mono (Nat.le_succ _)).add ho
        rwa [sub_add_cancel] at this
      have h4 := hlow _ (T.sub_mem hf (hT P hPA hP0)) N h3 n heq
      have h5 := h2 n hn
      rw [map_sub, sub_eq_zero] at h5
      rw [h5, map_sub, hP, if_neg (by omega), sub_zero] at h4
      exact h4
  exact fun n => main n.degree n (Nat.lt_succ_self _)

theorem funEq_mem [CharZero K] {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) {f : PowerSeries K}
    (h1 : PowerSeries.coeff 1 f = 1)
    (hden : ∀ n, ∃ k, p ^ k ∣ n ∧ (p : K) ^ k * PowerSeries.coeff n f ∈ A)
    (hg : ∀ n, PowerSeries.coeff n (f - (p : K)⁻¹ • f.subst (PowerSeries.X ^ q : PowerSeries K)) ∈ A)
    (Ψ : MvPowerSeries κ K →+* MvPowerSeries κ K)
    (hΨ0 : ∀ P, constantCoeff P = 0 → constantCoeff (Ψ P) = 0)
    (hΨf : ∀ P, constantCoeff P = 0 → Ψ (f.subst P) = f.subst (Ψ P))
    (hΨc : ∀ P ∈ intS A κ, ∃ y ∈ intS A κ, Ψ P = P ^ q + p * y)
    (hΨo : ∀ D N, HasOrd (N + 1) D → HasOrd (N + 2) (Ψ D))
    {t : MvPowerSeries κ K} (ht : constantCoeff t = 0)
    (hf : f.subst t - C (p : K)⁻¹ * Ψ (f.subst t) ∈ intS A κ) : t ∈ intS A κ := by
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp
  let L : MvPowerSeries κ K →+ MvPowerSeries κ K :=
    AddMonoidHom.id _ - (AddMonoidHom.mulLeft (C (p : K)⁻¹)).comp Ψ.toAddMonoidHom
  have hL : ∀ F, L F = F - C (p : K)⁻¹ * Ψ F := fun _ => rfl
  refine mem_of_subst_mem h1 ((intS A κ).toAddSubgroup.comap L) ?_ ?_ ht hf
  · intro P hP hP0
    change L _ ∈ intS A κ
    have hPS := PowerSeries.HasSubst.of_constantCoeff_zero hP0
    have hXq : PowerSeries.HasSubst (PowerSeries.X ^ q : PowerSeries K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hq])
    have hPq : constantCoeff (P ^ q) = 0 := by simp [hP0, hq]
    have e1 : (f - (p : K)⁻¹ • f.subst (PowerSeries.X ^ q : PowerSeries K)).subst P =
        f.subst P - C (p : K)⁻¹ * f.subst (P ^ q) := by
      rw [PowerSeries.subst_sub hPS, PowerSeries.subst_smul hPS, PowerSeries.subst_comp_subst_apply hXq hPS,
        PowerSeries.subst_pow hPS, PowerSeries.subst_X hPS, smul_eq_C_mul]
    have m1 := psubst_mem hPS hP hg
    obtain ⟨y, hy, hyP⟩ := hΨc P hP
    have m2 := psubst_sub_mem (A := A) (PowerSeries.HasSubst.of_constantCoeff_zero (hΨ0 P hP0))
      (PowerSeries.HasSubst.of_constantCoeff_zero hPq) f (p : K)⁻¹ (fun d => by
        obtain ⟨k, hk, hkA⟩ := hden d
        obtain ⟨z, hz, e⟩ := pow_congr (intS A κ) p ((intS A κ).pow_mem hP q) hy hyP hk
        have : C ((p : K)⁻¹ * PowerSeries.coeff d f) * ((p : MvPowerSeries κ K) ^ (k + 1) * z) =
            C ((p : K) ^ k * PowerSeries.coeff d f) * z := by
          rw [← map_natCast (C : K →+* MvPowerSeries κ K), ← map_pow, ← mul_assoc, ← map_mul]
          congr 2
          rw [pow_succ]
          field_simp
        rw [e, this]
        exact (intS A κ).mul_mem (C_mem hkA) hz)
    rw [e1] at m1
    rw [hL, hΨf P hP0]
    convert (intS A κ).sub_mem m1 m2 using 1
    ring
  · intro D hD N ho n hn
    have := (show L D ∈ intS A κ from hD) n
    rwa [hL, map_sub, coeff_C_mul, hΨo D N ho n (by omega), mul_zero, sub_zero] at this

theorem cc_exp_sub_one [CharZero K] : constantCoeff (PowerSeries.exp K - 1) = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.exp K - 1) = 0
  simp

theorem log_subst_exp_sub_one [CharZero K] :
    (PowerSeries.log K).subst (PowerSeries.exp K - 1) = (PowerSeries.X : PowerSeries K) := by
  have hs : PowerSeries.HasSubst (PowerSeries.exp K - 1) := PowerSeries.HasSubst.exp_sub_one
  have e : (1 + PowerSeries.X) * PowerSeries.derivative K (PowerSeries.log K) = 1 := by
    rw [PowerSeries.deriv_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, pow_succ]
  have e2 := congrArg (PowerSeries.substAlgHom (R := K) hs) e
  rw [map_mul, map_add, map_one, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom, add_sub_cancel] at e2
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [PowerSeries.derivative_subst hs, map_sub, PowerSeries.derivative_exp, PowerSeries.derivative_one,
      PowerSeries.derivative_X, sub_zero, mul_comm]
    exact e2
  · rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero cc_exp_sub_one _ PowerSeries.constantCoeff_log

theorem exp_mem [CharZero K] {p : ℕ} [hp : Fact p.Prime] {σ : K →+* K} (hu : ¬ IsUnit (p : A))
    (hσ : ∀ x ∈ A, ∃ y ∈ A, σ x = x ^ p + p * y) (hinv : ∀ n : ℕ, ¬ p ∣ n → (n : K)⁻¹ ∈ A)
    {H : MvPowerSeries κ K} (h0 : constantCoeff H = 0)
    (hH : H - C (p : K)⁻¹ * frob p hp.out.ne_zero σ κ H ∈ intS A κ) :
    (PowerSeries.exp K).subst H ∈ intS A κ := by
  have hp0 := hp.out.ne_zero
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero h0
  have hsg : ∀ n : ℕ, (-1 : K) ^ n ∈ A := fun n => A.pow_mem (A.neg_mem A.one_mem) n
  have hc : ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.log K) = (-1) ^ (n + 1) * (n : K)⁻¹ := fun n => by
    rw [PowerSeries.coeff_log]
    split_ifs with h
    · simp [h]
    · simp [div_eq_mul_inv]
  have e : (PowerSeries.log K).subst ((PowerSeries.exp K - 1).subst H) = H := by
    rw [← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.exp_sub_one hS, log_subst_exp_sub_one,
      PowerSeries.subst_X hS]
  have key : (PowerSeries.exp K - 1).subst H ∈ intS A κ := by
    refine funEq_mem hp0 hp0 PowerSeries.coeff_one_log (fun n => ?_) (fun n => ?_) (frob p hp0 σ κ)
      (fun P => constantCoeff_frob) (fun P hP => by rw [frob_psubst hP, PowerSeries.map_log])
      (fun P => frob_congr hu hσ) (fun D N => hasOrd_frob hp.out.two_le (by omega))
      (PowerSeries.constantCoeff_subst_eq_zero h0 _ (by simp)) (by rwa [e])
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨0, by simp, by simp [hc]⟩
      obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
      refine ⟨k, dvd_mul_right _ _, ?_⟩
      rw [hc]
      convert A.mul_mem (hsg (p ^ k * m + 1)) (hinv m hm) using 1
      push_cast
      field_simp
    · rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_subst_X_pow hp0, hc]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [Nat.mul_div_cancel_left _ hp.out.pos, hc]
        rcases hp.out.eq_two_or_odd' with rfl | ho
        · rcases Nat.even_or_odd m with hm | hm
          · convert A.zero_mem
            simp [pow_succ, hm.neg_one_pow, pow_mul]
            ring
          · convert A.neg_mem (hinv m (fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)))
            simp [pow_succ, hm.neg_one_pow, pow_mul]
            ring
        · convert A.zero_mem
          simp [pow_succ, ho.neg_one_pow, pow_mul]
          ring
      · simpa using A.mul_mem (hsg (n + 1)) (hinv n h)
  rw [PowerSeries.subst_sub hS, ← PowerSeries.coe_substAlgHom hS, map_one] at key
  have := (intS A κ).add_mem key (intS A κ).one_mem
  rwa [sub_add_cancel, PowerSeries.coe_substAlgHom] at this

end GlobalTheory.SubringSeries
