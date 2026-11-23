import Formalism.TorsionNormIteration.LTLemma
import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.LTL

open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP

section Near

variable {K : Type u} [NormedField K] {ι : Type*}

def Near (k : ℕ) (A B : MvPowerSeries ι K) : Prop := Low k A ∧ Low k B ∧ Low (k + 1) (A - B)

theorem Near.of_eq {k k' : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (hk : k = k') :
    Near k' A B := hk ▸ h

theorem Near.mul {k l : ℕ} {A B C D : MvPowerSeries ι K} (h1 : Near k A B) (h2 : Near l C D) :
    Near (k + l) (A * C) (B * D) := by
  refine ⟨h1.1.mul h2.1, h1.2.1.mul h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + B * (C - D) := by ring
  rw [e]
  exact ((h1.2.2.mul h2.1).mono (by omega)).add ((h1.2.1.mul h2.2.2).mono (by omega))

theorem near_one : Near 0 (1 : MvPowerSeries ι K) 1 :=
  ⟨low_zero _, low_zero _, fun d _ => by simp⟩

theorem Near.pow {k : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (n : ℕ) :
    Near (k * n) (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using near_one
  | succ n ih => rw [pow_succ, pow_succ]; exact (ih.mul h).of_eq (by ring)

theorem near_prod {τ : Type*} [DecidableEq ι] {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι → ℕ) (s : Finset ι) :
    Near (∑ i ∈ s, m i) (∏ i ∈ s, a i ^ m i) (∏ i ∈ s, b i ^ m i) := by
  induction s using Finset.induction_on with
  | empty => simpa using near_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    exact (((hab j).pow (m j)).mul ih).of_eq (by ring)

theorem near_monomial {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι →₀ ℕ) :
    Near m.degree (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by
  classical
  rw [Finsupp.degree_apply]
  exact near_prod hab m m.support

theorem low_subst_sub [Finite ι] {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Near 1 (a i) (b i)) {N : ℕ} {δ : MvPowerSeries ι K} (hδ : Low N δ) :
    Low (N + 1) (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by
  intro d hd
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d)
      (MvPowerSeries.coeff_subst_finite hb' δ d)]
  have : ∀ m : ι →₀ ℕ, MvPowerSeries.coeff m δ •
      MvPowerSeries.coeff d (m.prod fun s e => a s ^ e) - MvPowerSeries.coeff m δ •
      MvPowerSeries.coeff d (m.prod fun s e => b s ^ e) = 0 := by
    intro m
    rw [← smul_sub]
    by_cases hm : m.degree < N
    · rw [hδ m hm, zero_smul]
    · have := (near_monomial hab m).2.2 d (by omega)
      rw [map_sub] at this
      rw [this, smul_zero]
  simp only [this, finsum_zero]

end Near

section Master

variable {K : Type u} [NormedField K] {ι : Type*}

theorem decomp' (f : PowerSeries K) (h0 : constantCoeff f = 0) :
    f = coeff 1 f • X + X ^ 2 * tail2 f := by
  ext n
  rcases n with _ | _ | n
  · simp [h0]
  · simp [PowerSeries.coeff_X_pow_mul']
  · simp [tail2, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]

theorem subst_eq' (f : PowerSeries K) (h0 : constantCoeff f = 0) {a : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = coeff 1 f • a + a ^ 2 * (tail2 f).subst a := by
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  conv_lhs => rw [decomp' f h0]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_smul ha, PowerSeries.subst_mul ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

theorem key' [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) (f.subst a - f.subst b - coeff 1 f • (a - b)) := by
  rw [subst_eq' f h0 ha0, subst_eq' f h0 hb0]
  have e : coeff 1 f • a + a ^ 2 * (tail2 f).subst a - (coeff 1 f • b + b ^ 2 * (tail2 f).subst b)
      - coeff 1 f • (a - b) =
      a ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) + (a - b) * (a + b) * (tail2 f).subst b := by
    rw [smul_sub]; ring
  rw [e]
  refine Low.add ?_ ?_
  · have h2 : Low 2 (a ^ 2) := by
      rw [pow_two]; exact (low_one ha0).mul (low_one ha0)
    exact (h2.mul (low_of_agree (agree_psubst _ ha0 hb0 hab))).mono (by omega)
  · have hs : Low 1 (a + b) := (low_one ha0).add (low_one hb0)
    simpa using ((low_of_agree hab).mul hs).mul (low_zero ((tail2 f).subst b))

theorem near_one_subst_X_coeff_one_smul_X (f : PowerSeries K) (h0 : constantCoeff f = 0) (i : ι) :
    Near 1 (f.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      (((fun _ : ι => coeff 1 f) • (MvPowerSeries.X : ι → MvPowerSeries ι K)) i) := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by simp
  rw [subst_eq' f h0 hX]
  simp only [Pi.smul_apply']
  have hl : Low 1 (coeff 1 f • (MvPowerSeries.X i : MvPowerSeries ι K)) := low_one (by simp)
  refine ⟨?_, hl, ?_⟩
  · refine hl.add ?_
    have := ((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))
    rw [← pow_two] at this
    exact this.mono (by omega)
  · rw [add_sub_cancel_left]
    have := ((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))
    rw [← pow_two] at this
    exact this

theorem prod_const_pow (c : K) (d : ι →₀ ℕ) : (d.prod fun _ m => c ^ m) = c ^ d.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

def Ep (e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) x

def Ldef (e e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  Ep e' x - e.subst x

theorem inverseIntegralClasses_cc_s_fact (e' : PowerSeries K) (h0 : constantCoeff e' = 0) (i : ι) :
    MvPowerSeries.constantCoeff (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ h0

theorem Ep_sub [Finite ι] (e' : PowerSeries K) (h0 : constantCoeff e' = 0)
    (x y : MvPowerSeries ι K) : Ep e' x - Ep e' y = Ep e' (x - y) := by
  unfold Ep
  rw [MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero (inverseIntegralClasses_cc_s_fact e' h0))]

theorem master [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) (π : K) (he1 : coeff 1 e = π) (he'1 : coeff 1 e' = π)
    {N : ℕ} {ψ φ : MvPowerSeries ι K} (hψ : MvPowerSeries.constantCoeff ψ = 0)
    (hφ : MvPowerSeries.constantCoeff φ = 0) (hN : Low N (ψ - φ)) (d : ι →₀ ℕ)
    (hd : d.degree ≤ N) :
    MvPowerSeries.coeff d (Ldef e e' ψ) - MvPowerSeries.coeff d (Ldef e e' φ) =
      (π ^ N - π) * MvPowerSeries.coeff d (ψ - φ) := by
  have hag : Agree N ψ φ := fun d hd => by
    have := hN d hd; rw [map_sub] at this; exact sub_eq_zero.mp this
  have h1 := key' e he0 hψ hφ hag d (by omega)
  rw [he1] at h1
  simp only [map_sub, MvPowerSeries.coeff_smul] at h1
  have h2 := low_subst_sub (inverseIntegralClasses_cc_s_fact e' he'0) (fun i => by simp)
    (fun i => near_one_subst_X_coeff_one_smul_X e' he'0 i) hN d (by omega)
  rw [he'1, ← MvPowerSeries.rescale_eq_subst, map_sub, MvPowerSeries.coeff_rescale,
    prod_const_pow] at h2
  have h3 : MvPowerSeries.coeff d (Ep e' ψ) - MvPowerSeries.coeff d (Ep e' φ) =
      MvPowerSeries.coeff d (MvPowerSeries.subst
        (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) (ψ - φ)) := by
    rw [← map_sub, Ep_sub e' he'0]; rfl
  have h4 : π ^ d.degree * MvPowerSeries.coeff d (ψ - φ) =
      π ^ N * MvPowerSeries.coeff d (ψ - φ) := by
    rcases lt_or_eq_of_le hd with hlt | heq
    · rw [hN d hlt, mul_zero, mul_zero]
    · rw [heq]
  unfold Ldef
  simp only [map_sub] at h2 h4 ⊢
  linear_combination h3 + h2 + h4 - h1

end Master

section Cong

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

lemma norm_finsum_le' {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

theorem dv_add {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A + B) := fun d => by
  rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA d) (hB d))

theorem dv_neg {c : K} {A : MvPowerSeries ι K} (hA : DivByMv c A) :
    DivByMv c (-A) := fun d => by rw [map_neg, norm_neg]; exact hA d

theorem dv_sub {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A - B) := by rw [sub_eq_add_neg]; exact dv_add hA (dv_neg hB)

theorem dv_mul {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : IntegralMv B) :
    DivByMv c (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 A‖ * ‖MvPowerSeries.coeff p.2 B‖ ≤ ‖c‖ * 1 :=
        mul_le_mul (hA _) (hB _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

def Cong (c : K) (A B : MvPowerSeries ι K) : Prop :=
  IntegralMv A ∧ IntegralMv B ∧ DivByMv c (A - B)

theorem Cong.mul {c : K} {A B C D : MvPowerSeries ι K} (h1 : Cong c A B) (h2 : Cong c C D) :
    Cong c (A * C) (B * D) := by
  refine ⟨integral_mul h1.1 h2.1, integral_mul h1.2.1 h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + (C - D) * B := by ring
  rw [e]
  exact dv_add (dv_mul h1.2.2 h2.1) (dv_mul h2.2.2 h1.2.1)

theorem cong_one (c : K) : Cong c (1 : MvPowerSeries ι K) 1 :=
  ⟨integral_one, integral_one, fun d => by simp⟩

theorem Cong.pow {c : K} {A B : MvPowerSeries ι K} (h : Cong c A B) (n : ℕ) :
    Cong c (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using cong_one c
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem cong_monomial {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Cong c (a i) (b i)) (m : ι →₀ ℕ) :
    Cong c (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by
  classical
  unfold Finsupp.prod
  induction m.support using Finset.induction_on with
  | empty => simpa using cong_one c
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact ((hab j).pow (m j)).mul ih

theorem divBy_subst_sub [Finite ι] {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Cong c (a i) (b i)) {δ : MvPowerSeries ι K} (hδ : IntegralMv δ) :
    DivByMv c (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by
  intro d
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d)
      (MvPowerSeries.coeff_subst_finite hb' δ d)]
  refine norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [← smul_sub, smul_eq_mul, norm_mul, ← map_sub]
  calc _ ≤ 1 * ‖c‖ := mul_le_mul (hδ m) ((cong_monomial hab m).2.2 d) (norm_nonneg _) zero_le_one
    _ = ‖c‖ := one_mul _

theorem divBy_psubst (c : K) (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : DivBy c f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv c (f.subst P) := by
  intro d
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.coeff_subst ha f d]
  refine norm_finsum_le' (norm_nonneg _) fun n => ?_
  rw [smul_eq_mul, norm_mul]
  calc _ ≤ ‖c‖ * 1 := mul_le_mul (hf n) (integral_pow hP n d) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

end Cong

section FrobPi

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def piO (π : K) (hπ : ‖π‖ ≤ 1) : unitBall K := ⟨π, hπ⟩

theorem norm_le_of_mem_span' {π : K} (hπ : ‖π‖ ≤ 1) (x : unitBall K)
    (hx : x ∈ Ideal.span {piO π hπ}) : ‖(x : K)‖ ≤ ‖π‖ := by
  rw [Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : ‖(c : K)‖ ≤ 1 := c.2
  rw [Subring.coe_mul, norm_mul]
  calc ‖(c : K)‖ * ‖π‖ ≤ 1 * ‖π‖ := by gcongr
    _ = ‖π‖ := one_mul _

theorem mem_span_of_norm_le' {π : K} (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖π‖) : x ∈ Ideal.span {piO π hπ} := by
  rw [Ideal.mem_span_singleton']
  have hc : ‖(x : K) / π‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hx (norm_nonneg _)
  refine ⟨⟨(x : K) / π, hc⟩, ?_⟩
  apply Subtype.ext
  rw [Subring.coe_mul]
  change (x : K) / π * π = x
  field_simp

theorem frob_pi {ι : Type*} (p h : ℕ) (hpr : p.Prime) (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hp : ‖(p : K)‖ ≤ ‖π‖) (hF : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ (p ^ h) - a‖ ≤ ‖π‖)
    (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    DivByMv π (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A) := by
  have := Fact.mk hpr
  have hπ : ‖π‖ ≤ 1 := hπ1.le
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  set O := unitBall K
  set I : Ideal O := Ideal.span {piO π hπ}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : O) ∈ I := htop ▸ Submodule.mem_top
    have := norm_le_of_mem_span' hπ 1 h1
    simp at this
    linarith
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hpI : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    apply mem_span_of_norm_le' hπ hπne
    simpa using hp
  have : CharP (O ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpr).mpr hpI
  have : ExpChar (O ⧸ I) p := ExpChar.prime hpr
  set mk := Ideal.Quotient.mk I
  set A' := Formalism.LT.FrobP.liftO A hA
  set B' : MvPowerSeries ι O := A' ^ (p ^ h) - MvPowerSeries.expand (p ^ h)
    (pow_ne_zero h hpr.ne_zero) A'
  have hB : A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A =
      MvPowerSeries.map O.subtype B' := by
    simp only [B', map_sub, map_pow, MvPowerSeries.map_expand]
    rw [show MvPowerSeries.map O.subtype A' = A from Formalism.LT.FrobP.map_liftO A hA]
  have hcomp : (iterateFrobenius (O ⧸ I) p h).comp mk = mk := by
    ext a
    simp only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    rw [Ideal.Quotient.eq]
    apply mem_span_of_norm_le' hπ hπne
    exact hF a.1 a.2
  have hzero : MvPowerSeries.map mk B' = 0 := by
    simp only [B', map_sub, map_pow, MvPowerSeries.map_expand]
    rw [← MvPowerSeries.map_iterateFrobenius_expand _ hpr.ne_zero, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_map, hcomp, sub_self]
  intro d
  rw [hB, MvPowerSeries.coeff_map]
  apply norm_le_of_mem_span' hπ
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (MvPowerSeries.coeff d) hzero
  simpa [MvPowerSeries.coeff_map] using this

end FrobPi

section Defect

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem integralMv_X' (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem defect_divBy [Finite ι] {p q : ℕ} {π : K} (hS : LTSetting K p q π)
    {e e' : PowerSeries K} (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {P : MvPowerSeries ι K} (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv π (Ldef e e' P) := by
  obtain ⟨hpr, ⟨h, hh, rfl⟩, hπ0, hπ1, hp, hF⟩ := hS
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0

  have h1 : DivByMv π (e.subst P - P ^ (p ^ h)) := by
    have := divBy_psubst π (e - X ^ (p ^ h)) P he.2.2.2 hP0 hP
    rwa [PowerSeries.subst_sub ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha] at this
  have h2 := frob_pi p h hpr π hπ0 hπ1 hp hF P hP
  have hXq : ∀ i : ι, MvPowerSeries.constantCoeff
      ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) = 0 := fun i => by
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]
  have hcong : ∀ i : ι, Cong π (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) := by
    intro i
    have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by simp
    have hXs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hX0
    refine ⟨integralSubst e' _ he'.1 hX0 (integralMv_X' i), integral_pow (integralMv_X' i) _, ?_⟩
    have := divBy_psubst π (e' - X ^ (p ^ h)) (MvPowerSeries.X i : MvPowerSeries ι K) he'.2.2.2
      hX0 (integralMv_X' i)
    rwa [PowerSeries.subst_sub hXs, PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs] at this
  have h3 : DivByMv π (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) := by
    have := divBy_subst_sub (inverseIntegralClasses_cc_s_fact e' he'.2.1) hXq hcong hP
    rwa [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  have e4 : Ldef e e' P = (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) -
      (P ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq P) - (e.subst P - P ^ (p ^ h)) := by
    unfold Ldef; ring
  rw [e4]
  exact dv_sub (dv_sub h3 h2) h1

theorem norm_pi_sub_pow {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {r : ℕ} (hr : 2 ≤ r) :
    ‖π - π ^ r‖ = ‖π‖ := by
  have hlt : ‖π ^ r‖ < ‖π‖ := by
    rw [norm_pow]; exact pow_lt_self_of_lt_one₀ hπ0 hπ1 (by omega)
  apply le_antisymm
  · have := IsUltrametricDist.norm_add_le_max π (-(π ^ r))
    rw [← sub_eq_add_neg, norm_neg] at this
    exact this.trans (max_le le_rfl hlt.le)
  · have := IsUltrametricDist.norm_add_le_max (π - π ^ r) (π ^ r)
    rw [sub_add_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)

end Defect

section Constr

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem Ep_zero [Finite ι] (e' : PowerSeries K) (he'0 : constantCoeff e' = 0) :
    Ep e' (0 : MvPowerSeries ι K) = 0 := by
  have := Ep_sub e' he'0 (0 : MvPowerSeries ι K) 0
  rw [sub_self, sub_self] at this
  exact this.symm

theorem Ldef_zero [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) : Ldef e e' (0 : MvPowerSeries ι K) = 0 := by
  unfold Ldef
  rw [Ep_zero e' he'0, PowerSeries.subst_zero_of_constantCoeff_zero he0, sub_zero]

variable [Fintype ι] [DecidableEq ι]

def lin (a : ι → K) : MvPowerSeries ι K := ∑ i, a i • MvPowerSeries.X i

theorem cc_lin (a : ι → K) : MvPowerSeries.constantCoeff (lin a) = 0 := by
  simp [lin]

theorem coeff_lin (a : ι → K) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (lin a) = ∑ i, a i * (if d = Finsupp.single i 1 then 1 else 0) := by
  simp only [lin, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X]

theorem coeff_lin_single (a : ι → K) (i : ι) :
    MvPowerSeries.coeff (Finsupp.single i 1) (lin a) = a i := by
  rw [coeff_lin]
  simp [Finsupp.single_left_inj one_ne_zero]

theorem integral_lin (a : ι → K) (ha : ∀ i, ‖a i‖ ≤ 1) : IntegralMv (lin a) := by
  intro d
  rw [coeff_lin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  split_ifs <;> simp [ha i]

def corr (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun d => if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0

theorem coeff_corr (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K)
    (d : ι →₀ ℕ) : MvPowerSeries.coeff d (corr e e' π N P) =
      if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0 :=
  rfl

def seq (e e' : PowerSeries K) (π : K) (a : ι → K) : ℕ → MvPowerSeries ι K
  | 0 => 0
  | 1 => lin a
  | (N + 2) => seq e e' π a (N + 1) + corr e e' π (N + 1) (seq e e' π a (N + 1))

def Inv (e e' : PowerSeries K) (a : ι → K) (k : ℕ) (P : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.constantCoeff P = 0 ∧ IntegralMv P ∧
    (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) P = a i) ∧ Low (k + 1) (Ldef e e' P)

variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

theorem step_inv (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {N : ℕ} (hN : 1 ≤ N) {P : MvPowerSeries ι K} (h : Inv e e' a N P) :
    Inv e e' a (N + 1) (P + corr e e' π N P) ∧ Low (N + 1) (corr e e' π N P) := by
  have hπ0 : 0 < ‖π‖ := hS.2.2.1
  have hπ1 : ‖π‖ < 1 := hS.2.2.2.1
  have hnorm := norm_pi_sub_pow hπ0 hπ1 (r := N + 1) (by omega)
  have hne : π - π ^ (N + 1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; linarith
  have hlowc : Low (N + 1) (corr e e' π N P) := by
    intro d hd; rw [coeff_corr, if_neg (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hlowc⟩
  · rw [map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp),
      add_zero]
  · intro d
    rw [map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.2.1 d) ?_)
    rw [coeff_corr]
    split_ifs
    · rw [norm_div, hnorm]
      exact div_le_one_of_le₀ (defect_divBy hS he he' h.1 h.2.1 d) (norm_nonneg _)
    · simp
  · intro i
    rw [map_add, h.2.2.1 i, hlowc _ (by rw [Finsupp.degree_single]; omega), add_zero]
  · have hP'0 : MvPowerSeries.constantCoeff (P + corr e e' π N P) = 0 := by
      rw [map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp),
        add_zero]
    have hdiff : Low (N + 1) (P + corr e e' π N P - P) := by
      rw [add_sub_cancel_left]; exact hlowc
    intro d hd
    have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hP'0 h.1 hdiff d (by omega)
    rw [add_sub_cancel_left, coeff_corr] at hm
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
    · rw [if_neg (by omega), mul_zero, h.2.2.2 d hlt, sub_zero] at hm
      exact hm
    · rw [if_pos heq] at hm
      have : (π ^ (N + 1) - π) * (MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1))) =
          -MvPowerSeries.coeff d (Ldef e e' P) := by
        field_simp; ring
      linear_combination hm + this

theorem inv_lin (_hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) : Inv e e' a 1 (lin a) := by
  refine ⟨cc_lin a, integral_lin a ha, coeff_lin_single a, ?_⟩
  intro d hd
  have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 (cc_lin a)
    (map_zero _) (by rw [sub_zero]; exact low_one (cc_lin a)) d (by omega)
  rw [Ldef_zero e e' he.2.1 he'.2.1, map_zero, pow_one, sub_self, zero_mul, sub_zero] at hm
  exact hm

theorem inv_seq (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) : ∀ k : ℕ, Inv e e' a (k + 1) (seq e e' π a (k + 1))
  | 0 => inv_lin hS he he' ha
  | (k + 1) => (step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).1

theorem seq_sub (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) (k : ℕ) :
    Low (k + 2) (seq e e' π a (k + 2) - seq e e' π a (k + 1)) := by
  have := (step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).2
  change Low (k + 2) (seq e e' π a (k + 1) + corr e e' π (k + 1) (seq e e' π a (k + 1)) -
    seq e e' π a (k + 1))
  rw [add_sub_cancel_left]; exact this

theorem stab (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) (d : ι →₀ ℕ) : ∀ k : ℕ, d.degree < k + 1 →
    MvPowerSeries.coeff d (seq e e' π a (k + 1)) =
      MvPowerSeries.coeff d (seq e e' π a (d.degree + 1)) := by
  intro k
  induction k with
  | zero => intro hd; rw [show d.degree = 0 by omega]
  | succ j ih =>
    intro hd
    by_cases h : d.degree = j + 1
    · rw [h]
    · rw [← ih (by omega)]
      have := seq_sub hS he he' ha j d (by omega)
      rw [map_sub] at this
      exact sub_eq_zero.mp this

def lim (e e' : PowerSeries K) (π : K) (a : ι → K) : MvPowerSeries ι K :=
  fun d => MvPowerSeries.coeff d (seq e e' π a (d.degree + 1))

theorem uniq (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {ψ φ : MvPowerSeries ι K} (hψ0 : MvPowerSeries.constantCoeff ψ = 0)
    (hφ0 : MvPowerSeries.constantCoeff φ = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) ψ =
      MvPowerSeries.coeff (Finsupp.single i 1) φ)
    (hLψ : Ldef e e' ψ = 0) (hLφ : Ldef e e' φ = 0) : ψ = φ := by
  have hπ0 : 0 < ‖π‖ := hS.2.2.1
  have hπ1 : ‖π‖ < 1 := hS.2.2.2.1
  have H : ∀ N : ℕ, Low (N + 2) (ψ - φ) := by
    intro N
    induction N with
    | zero =>
      intro d hd
      rw [map_sub, sub_eq_zero]
      rcases Nat.lt_or_ge d.degree 1 with h0 | h0
      · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
        subst this
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0, hφ0]
      · obtain ⟨i, hi⟩ : ∃ i, d = Finsupp.single i 1 := by
          have hd1 : d.degree = 1 := by omega
          obtain ⟨i, hi⟩ : d.support.Nonempty := by
            rw [Finsupp.support_nonempty_iff]
            rintro rfl
            simp at hd1
          refine ⟨i, ?_⟩
          have hle : Finsupp.single i (d i) ≤ d := by
            intro j
            by_cases hj : j = i
            · subst hj; simp
            · simp [Ne.symm hj]
          have hdi : d i = 1 := by
            have h2 := Finsupp.degree_mono hle
            rw [Finsupp.degree_single] at h2
            have : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
            omega
          obtain ⟨r, hr⟩ := le_iff_exists_add.mp hle
          have : r.degree = 0 := by
            have := congrArg Finsupp.degree hr
            rw [map_add, Finsupp.degree_single] at this
            omega
          rw [(Finsupp.degree_eq_zero_iff r).mp this, add_zero, hdi] at hr
          exact hr
        subst hi
        exact h1 i
    | succ N ih =>
      intro d hd
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
      · exact ih d hlt
      · have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hψ0 hφ0 ih d (by omega)
        rw [hLψ, hLφ, map_zero, sub_zero] at hm
        have hnorm := norm_pi_sub_pow hπ0 hπ1 (r := N + 2) (by omega)
        have hne : π ^ (N + 2) - π ≠ 0 := by
          intro h0
          rw [← neg_sub, h0, neg_zero, norm_zero] at hnorm
          linarith
        exact (mul_eq_zero.mp hm.symm).resolve_left hne
  ext d
  have := H d.degree d (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

end Constr

end Formalism.LT.LTL

namespace Formalism.LT

open Formalism.G Formalism.LT.LTL

end Formalism.LT
