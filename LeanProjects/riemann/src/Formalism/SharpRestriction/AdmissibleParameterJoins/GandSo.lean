import Mathlib

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries

section AlgebraTools

variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]

def diagS (a : PowerSeries R) (i : ι) : MvPowerSeries ι R := PowerSeries.subst (X i : MvPowerSeries ι R) a

private theorem powerSeries_hasSubst_of_constantCoeff_eq_zero {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    PowerSeries.HasSubst f := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hf
  | (show IsNilpotent _; rw [hf]; exact IsNilpotent.zero)

private theorem coeff_diagS [DecidableEq ι] (a : PowerSeries R) (i : ι) (e : ι →₀ ℕ) :
    coeff e (diagS a i : MvPowerSeries ι R) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) a else 0 := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries ι R) := powerSeries_hasSubst_of_constantCoeff_eq_zero (constantCoeff_X i)
  unfold diagS
  rw [PowerSeries.coeff_subst hX]
  have hterm : ∀ d : ℕ, PowerSeries.coeff d a • coeff e ((X i : MvPowerSeries ι R) ^ d) =
      if e = Finsupp.single i d then PowerSeries.coeff d a else 0 := by
    intro d
    first
    | (rw [MvPowerSeries.coeff_X_pow, smul_eq_mul]; split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]; split_ifs <;> simp)
  simp_rw [hterm]
  rw [finsum_eq_single _ (e i)]
  intro d hd
  have hne : ¬ e = Finsupp.single i d := fun he => hd (by rw [he, Finsupp.single_eq_same])
  simp [hne]

private theorem coeff_diagS_eq_zero_of_apply_eq_zero {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (i : ι) (d : ι →₀ ℕ) (hd : d i = 0) : coeff d (diagS a i : MvPowerSeries ι R) = 0 := by
  classical
  rw [coeff_diagS]
  split_ifs
  · rw [hd, PowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
  · rfl

theorem cc_dg {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) (i : ι) :
    constantCoeff (diagS a i : MvPowerSeries ι R) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_diagS_eq_zero_of_apply_eq_zero ha i 0 (by simp)

theorem hs_dg {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    HasSubst (diagS a : ι → MvPowerSeries ι R) where
  const_coeff s := by rw [cc_dg ha]; exact IsNilpotent.zero
  coeff_zero d := by
    classical
    refine (d.support.finite_toSet).subset ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    unfold diagS at hs
    rw [PowerSeries.coeff_subst_single] at hs
    by_contra hns
    have h0 : d s = 0 := by simpa using hns
    split_ifs at hs with h1
    · rw [h0] at hs
      exact hs (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ha])
    · exact hs rfl

private theorem hasSubst_of_finite_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, constantCoeff (c s) = 0) : HasSubst c := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hc

theorem subst_psubst {c : ι → MvPowerSeries κ R} (hc : HasSubst c) {f : MvPowerSeries ι R}
    (hf : constantCoeff f = 0) (a : PowerSeries R) :
    subst c (PowerSeries.subst f a) = PowerSeries.subst (subst c f) a := by
  have hf' : HasSubst (fun _ : Unit => f) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hf)
  first
  | exact MvPowerSeries.subst_comp_subst_apply hf' hc a
  | (rw [PowerSeries.subst, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hf' hc])

theorem dg_comp {a b : PowerSeries R} (hb : PowerSeries.constantCoeff b = 0) (i : ι) :
    subst (diagS b) (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.subst b a) i := by
  have hc : HasSubst (diagS b : ι → MvPowerSeries ι R) := hs_dg hb
  have hXi : constantCoeff (X i : MvPowerSeries ι R) = 0 := constantCoeff_X i
  have hb' : constantCoeff (b : MvPowerSeries Unit R) = 0 := hb
  have hu : HasSubst (fun _ : Unit => (X i : MvPowerSeries ι R)) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hXi)
  calc subst (diagS b) (diagS a i : MvPowerSeries ι R)
      = PowerSeries.subst (subst (diagS b) (X i : MvPowerSeries ι R)) a :=
        subst_psubst hc hXi a
    _ = PowerSeries.subst (diagS b i) a := by rw [MvPowerSeries.subst_X hc]
    _ = PowerSeries.subst (subst (fun _ : Unit => (X i : MvPowerSeries ι R)) b) a := rfl
    _ = subst (fun _ : Unit => (X i : MvPowerSeries ι R)) (PowerSeries.subst b a) :=
        (subst_psubst hu hb' a).symm
    _ = diagS (PowerSeries.subst b a) i := rfl

theorem map_dg (h : R →+* S) (a : PowerSeries R) (i : ι) :
    map h (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.map h a) i := by
  classical
  ext e
  rw [MvPowerSeries.coeff_map, coeff_diagS, coeff_diagS]
  split_ifs
  · rw [PowerSeries.coeff_map]
  · exact map_zero h

theorem dg_X (i : ι) : (diagS (PowerSeries.X : PowerSeries R) i : MvPowerSeries ι R) = X i := by
  classical
  ext e
  rw [coeff_diagS, MvPowerSeries.coeff_X, PowerSeries.coeff_X]
  by_cases h3 : e = Finsupp.single i 1
  · subst h3
    simp
  · rw [if_neg h3]
    split_ifs with h1 h2
    · exact absurd (h1.trans (congrArg (Finsupp.single i) h2)) h3
    · rfl
    · rfl

private theorem diagS_unit (a : PowerSeries R) :
    (diagS a () : MvPowerSeries Unit R) = (a : MvPowerSeries Unit R) := by
  refine MvPowerSeries.ext fun e => ?_
  have he : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by
    cases u
    rw [Finsupp.single_eq_same]
  rw [coeff_diagS, if_pos he]
  conv_rhs => rw [he]
  rfl

private theorem constantCoeff_powerSeries_subst_eq_zero_admissible_parameter_joins {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0)
    {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    constantCoeff (PowerSeries.subst f a) = 0 := by
  obtain ⟨b, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
  first
  | rw [PowerSeries.subst_mul (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), PowerSeries.subst_X (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, hf, zero_mul]
  | rw [← PowerSeries.coe_substAlgHom (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, hf, zero_mul]

theorem coeff_pow_zero {f : MvPowerSeries ι R} (hf : constantCoeff f = 0) :
    ∀ (d : ℕ) (n : ι →₀ ℕ), n.degree < d → coeff n (f ^ d) = 0 := by
  classical
  intro d
  induction d with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero _)
  | succ d ih =>
    intro n hn
    rw [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    replace hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases h2 : p.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]
    · have hdeg : p.1.degree + p.2.degree = n.degree := by
        rw [← hp]
        first
        | exact (Finsupp.degree_add p.1 p.2).symm
        | exact (map_add Finsupp.degree p.1 p.2).symm
        | simp [Finsupp.degree_add]
      have hpos : p.2.degree ≠ 0 := by
        intro h
        apply h2
        first
        | exact (Finsupp.degree_eq_zero_iff _).mp h
        | exact Finsupp.degree_eq_zero_iff.mp h
      rw [ih p.1 (by omega), zero_mul]

end AlgebraTools

section Exp

variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']

def Ex (f : MvPowerSeries ι K) : MvPowerSeries ι K := PowerSeries.subst f (PowerSeries.exp K)

theorem subst_Ex {c : ι → MvPowerSeries κ K} (hc : HasSubst c) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : subst c (Ex f) = Ex (subst c f) := by
  exact subst_psubst hc hf (PowerSeries.exp K)

private theorem coeff_Ex_eq_sum_inv_factorial_coeff_pow {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) (n : ι →₀ ℕ) :
    coeff n (Ex f) =
      ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by
  unfold Ex
  rw [PowerSeries.coeff_subst (powerSeries_hasSubst_of_constantCoeff_eq_zero hf)]
  have key : ∀ k, k ∉ Finset.range (n.degree + 1) →
      PowerSeries.coeff k (PowerSeries.exp K) • coeff n (f ^ k) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [coeff_pow_zero hf k n (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n.degree + 1))
    (fun k hk => by
      by_contra h
      exact hk (key k h))]
  apply Finset.sum_congr rfl
  intro k _
  simp [PowerSeries.coeff_exp, smul_eq_mul]

theorem map_Ex (h : K →+* K') {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    map h (Ex f) = Ex (map h f) := by
  ext n
  have hf' : constantCoeff (map h f) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hf, map_zero]
  rw [MvPowerSeries.coeff_map, coeff_Ex_eq_sum_inv_factorial_coeff_pow hf, coeff_Ex_eq_sum_inv_factorial_coeff_pow hf', map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, map_inv₀, map_natCast, ← map_pow (MvPowerSeries.map h) f k, MvPowerSeries.coeff_map]

theorem Ex_zero : Ex (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_Ex_eq_sum_inv_factorial_coeff_pow (f := (0 : MvPowerSeries ι K)) (by simp), Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

private theorem coeff_X_zero_add_X_one_pow (n : Fin 2 →₀ ℕ) (k : ℕ) :
    coeff n ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ k) =
      if k = n 0 + n 1 then ((k.choose (n 0) : ℕ) : K) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      coeff n ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (k - m) *
        ((k.choose m : ℕ) : MvPowerSeries (Fin 2) K)) =
        if n = Finsupp.single 0 m + Finsupp.single 1 (k - m) then ((k.choose m : ℕ) : K) else 0 := by
    intro m _
    first
    | (rw [← nsmul_eq_mul', map_nsmul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul, MvPowerSeries.coeff_monomial, nsmul_eq_mul]
       split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
        ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
        MvPowerSeries.coeff_monomial]
       split_ifs <;> simp)
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hk
  · rw [Finset.sum_eq_single (n 0)]
    · rw [if_pos]
      ext i
      fin_cases i <;> simp [hk]
    · intro m _ hm
      rw [if_neg]
      intro h
      apply hm
      have h0 := congrArg (fun e => e 0) h
      simp at h0
      omega
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro h
    apply hk
    have h0 := congrArg (fun e => e 0) h
    have h1 := congrArg (fun e => e 1) h
    simp at h0 h1
    rw [Finset.mem_range] at hm
    omega

theorem Ex_biv : Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K) = Ex (X 0) * Ex (X 1) := by
  ext n
  have hs : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hL : coeff n (Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff (n 0 + n 1) (PowerSeries.exp K) * (((n 0 + n 1).choose (n 0) : ℕ) : K) := by
    unfold Ex
    rw [PowerSeries.coeff_subst (powerSeries_hasSubst_of_constantCoeff_eq_zero hs)]
    simp_rw [coeff_X_zero_add_X_one_pow]
    rw [finsum_eq_single _ (n 0 + n 1)]
    · simp
    · intro d hd
      simp [hd]
  have hR : coeff n (Ex (X 0 : MvPowerSeries (Fin 2) K) * Ex (X 1)) =
      PowerSeries.coeff (n 0) (PowerSeries.exp K) * PowerSeries.coeff (n 1) (PowerSeries.exp K) := by
    change coeff n (diagS (PowerSeries.exp K) 0 * diagS (PowerSeries.exp K) 1) = _
    rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (n 0), Finsupp.single 1 (n 1))]
    · rw [coeff_diagS, coeff_diagS]
      simp
    · intro p hp hne
      replace hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [coeff_diagS, coeff_diagS]
      by_cases h1 : p.1 = Finsupp.single 0 (p.1 0)
      · by_cases h2 : p.2 = Finsupp.single 1 (p.2 1)
        · exfalso
          apply hne
          have e0 := congrArg (fun e => e 0) hp
          have e1 := congrArg (fun e => e 1) hp
          rw [h2] at e0
          rw [h1] at e1
          simp at e0 e1
          exact Prod.ext (h1.trans (congrArg (Finsupp.single 0) e0))
            (h2.trans (congrArg (Finsupp.single 1) e1))
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      refine Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_
      ext i
      fin_cases i <;> simp
  rw [hL, hR]
  simp only [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
  rw [Nat.cast_add_choose]
  have hne : ((n 0 + n 1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  first
  | (rw [div_mul_div_comm, one_mul, div_mul_cancel_left₀ hne]; simp)
  | (field_simp; done)
  | (field_simp; rw [mul_inv_cancel₀ hne, one_mul])
  | (field_simp; simp [hne])
  all_goals first | ring | exact mul_comm _ _

theorem Ex_add {f g : MvPowerSeries ι K} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    Ex (f + g) = Ex f * Ex g := by
  have hc : HasSubst (![f, g] : Fin 2 → MvPowerSeries ι K) :=
    hasSubst_of_finite_constantCoeff_eq_zero (by intro i; fin_cases i <;> simp [hf, hg])
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have key := congrArg (subst (![f, g] : Fin 2 → MvPowerSeries ι K)) (Ex_biv (K := K))
  rw [subst_Ex hc h01, MvPowerSeries.subst_mul hc, subst_Ex hc h0, subst_Ex hc h1,
    MvPowerSeries.subst_add hc, MvPowerSeries.subst_X hc, MvPowerSeries.subst_X hc] at key
  simpa using key

theorem Ex_neg_mul {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) : Ex (-f) * Ex f = 1 := by
  have hn : constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [← Ex_add hn hf]
  simp [Ex_zero]

theorem coeff_Ex {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) (n : ι →₀ ℕ) :
    coeff n (Ex f) = ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ * coeff n (f ^ k) := by
  exact coeff_Ex_eq_sum_inv_factorial_coeff_pow hf n

end Exp

section Int

variable {ι κ : Type} {K : Type} [Field K]

theorem exists_lift (O : Subring K) (A : MvPowerSeries ι K) (h : ∀ n, coeff n A ∈ O) :
    ∃ A' : MvPowerSeries ι O, map O.subtype A' = A := by
  refine ⟨fun n => ⟨coeff n A, h n⟩, ?_⟩
  ext n
  first
  | rfl
  | (erw [MvPowerSeries.coeff_map]; rfl)

private theorem finsum_mem_subring (O : Subring K) {α : Type} (F : α → K) (hF : ∀ x, F x ∈ O) :
    ∑ᶠ x, F x ∈ O := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_sum F hfin]
    exact Subring.sum_mem O (fun x _ => hF x)
  · rw [finsum_of_infinite_support hfin]
    exact O.zero_mem

private theorem mem_range_map_subring_iff {σ : Type} (O : Subring K) (F : MvPowerSeries σ K) :
    F ∈ (MvPowerSeries.map (σ := σ) O.subtype).range ↔ ∀ n, coeff n F ∈ O := by
  constructor
  · intro hF n
    obtain ⟨F', rfl⟩ := RingHom.mem_range.mp hF
    rw [MvPowerSeries.coeff_map]
    exact (coeff n F').2
  · intro hF
    obtain ⟨F', hF'⟩ := exists_lift O F hF
    exact RingHom.mem_range.mpr ⟨F', hF'⟩

private theorem coeff_subst_mem_subring {σ τ : Type} (O : Subring K) (A : MvPowerSeries σ K)
    (hA : ∀ n, coeff n A ∈ O) (c : σ → MvPowerSeries τ K) (hc : HasSubst c)
    (hcO : ∀ i n, coeff n (c i) ∈ O) : ∀ n, coeff n (subst c A) ∈ O := by
  intro e
  rw [MvPowerSeries.coeff_subst hc]
  apply finsum_mem_subring
  intro d
  simp only [smul_eq_mul]
  refine O.mul_mem (hA d) ?_
  have hmem : (d.prod fun s k => c s ^ k) ∈ (MvPowerSeries.map (σ := τ) O.subtype).range := by
    simp only [Finsupp.prod]
    apply Subring.prod_mem
    intro s _
    exact Subring.pow_mem _ ((mem_range_map_subring_iff O (c s)).mpr (hcO s)) _
  exact (mem_range_map_subring_iff O _).mp hmem e

theorem int_subst [Finite ι] (O : Subring K) (A : MvPowerSeries ι K) (hA : ∀ n, coeff n A ∈ O)
    (c : ι → MvPowerSeries κ K) (hc0 : ∀ i, constantCoeff (c i) = 0) (hc : ∀ i n, coeff n (c i) ∈ O) :
    ∀ n, coeff n (subst c A) ∈ O := by
  exact coeff_subst_mem_subring O A hA c (hasSubst_of_finite_constantCoeff_eq_zero hc0) hc

theorem int_dg (O : Subring K) (a : PowerSeries K) (ha : ∀ n, PowerSeries.coeff n a ∈ O) (i : ι) (n : ι →₀ ℕ) :
    coeff n (diagS a i : MvPowerSeries ι K) ∈ O := by
  classical
  rw [coeff_diagS]
  split_ifs
  · exact ha _
  · exact O.zero_mem

theorem exists_plift (O : Subring K) (a : PowerSeries K) (h : ∀ n, PowerSeries.coeff n a ∈ O) :
    ∃ a' : PowerSeries O, PowerSeries.map O.subtype a' = a := by
  refine ⟨PowerSeries.mk (fun n => ⟨PowerSeries.coeff n a, h n⟩), ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rfl

theorem int_subst_dg (O : Subring K) (A : MvPowerSeries ι K) (hA : ∀ n, coeff n A ∈ O) (a : PowerSeries K)
    (ha0 : PowerSeries.constantCoeff a = 0) (ha : ∀ n, PowerSeries.coeff n a ∈ O) :
    ∀ n, coeff n (subst (diagS a) A) ∈ O := by
  exact coeff_subst_mem_subring O A hA (diagS a) (hs_dg ha0)
    (fun i n => int_dg O a ha i n)

theorem descent (O : Subring K) (th lg ps : PowerSeries K) (hth0 : PowerSeries.constantCoeff th = 0)
    (hps0 : PowerSeries.constantCoeff ps = 0) (hpsO : ∀ n, PowerSeries.coeff n ps ∈ O)
    (hinv : PowerSeries.subst ps th = PowerSeries.X) (hlg0 : PowerSeries.constantCoeff lg = 0)
    (G : MvPowerSeries ι K) (h : ∀ n, coeff n (subst (diagS (PowerSeries.subst th lg)) G) ∈ O) :
    ∀ n, coeff n (subst (diagS lg) G) ∈ O := by
  have hthlg : constantCoeff (PowerSeries.subst th lg) = 0 := constantCoeff_powerSeries_subst_eq_zero_admissible_parameter_joins hth0 hlg0
  have hcomp : PowerSeries.subst ps (PowerSeries.subst th lg) = lg := by
    have hu : HasSubst (fun _ : Unit => ps) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hps0)
    have h1 : PowerSeries.subst ps (PowerSeries.subst th lg) =
        PowerSeries.subst (PowerSeries.subst ps th) lg :=
      subst_psubst hu hth0 lg
    rw [h1, hinv]
    exact diagS_unit lg
  have key : subst (diagS ps) (subst (diagS (PowerSeries.subst th lg)) G) =
      subst (diagS lg) G := by
    rw [MvPowerSeries.subst_comp_subst_apply (hs_dg hthlg) (hs_dg hps0)]
    congr 1
    funext i
    rw [dg_comp hps0 i, hcomp]
  rw [← key]
  exact int_subst_dg O _ h ps hps0 hpsO

end Int

end Formalism.MainNotions.J
