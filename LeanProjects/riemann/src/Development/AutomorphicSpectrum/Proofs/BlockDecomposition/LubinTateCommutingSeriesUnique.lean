import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.QGal

theorem ltIter_succ {A : Type} [CommRing A] (w : A) (q n : ℕ) (x : A) :
    ltIter w q (n + 1) x = w * ltIter w q n x + ltIter w q n x ^ q := by
  simp only [ltIter, Function.iterate_succ_apply']

theorem map_ltIter {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') (a : A) (q n : ℕ) (x : A) :
    g (ltIter a q n x) = ltIter (g a) q n (g x) := by
  induction n with
  | zero => simp [ltIter]
  | succ n ih => rw [ltIter_succ, ltIter_succ, map_add, map_mul, map_pow, ih]

theorem ltIter_congr {A : Type} [CommRing A] (w s : A) (q : ℕ) (hq : (q : A) = w * s) (a b c : A)
    (h : a - b = w * c) (n : ℕ) : ∃ d, ltIter w q n a - ltIter w q n b = w ^ (n + 1) * d := by
  induction n with
  | zero => exact ⟨c, by simpa [ltIter] using h⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    rw [ltIter_succ, ltIter_succ]
    generalize ltIter w q n a = x at hd ⊢
    generalize ltIter w q n b = y at hd ⊢
    have hx : x = y + w ^ (n + 1) * d := by linear_combination hd
    obtain ⟨k, hk⟩ := Polynomial.powAddExpansion y (w ^ (n + 1) * d) q
    refine ⟨d + s * y ^ (q - 1) * d + k * w ^ n * d ^ 2, ?_⟩
    rw [hx, hk, hq]
    ring

theorem nil_ltIter {A : Type} [CommRing A] (w : A) {q : ℕ} (hq : q ≠ 0) {y : A} (hy : IsNilpotent y) (n : ℕ) :
    IsNilpotent (ltIter w q n y) := by
  induction n with
  | zero => simpa [ltIter] using hy
  | succ n ih =>
    rw [ltIter_succ]
    rw [← mem_nilradical] at ih ⊢
    exact add_mem (Ideal.mul_mem_left _ _ ih) (Ideal.pow_mem_of_mem _ ih q (Nat.pos_of_ne_zero hq))

section Nil

variable {R C : Type} [CommRing R] [CommRing C] [Algebra R C]

def nev (y : C) (φ : PowerSeries R) : C :=
  PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C y : PowerSeries C) φ : PowerSeries C)

theorem hasSubst_C {y : C} (hy : IsNilpotent y) : PowerSeries.HasSubst (PowerSeries.C y : PowerSeries C) := by
  have h : MvPowerSeries.constantCoeff (PowerSeries.C y : PowerSeries C) = y := PowerSeries.constantCoeff_C y
  simpa [PowerSeries.HasSubst, h] using hy

theorem subst_lt {a : PowerSeries C} (ha : PowerSeries.HasSubst a) (π : R) (q : ℕ) :
    (PowerSeries.subst a (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) : PowerSeries C)
      = PowerSeries.C (algebraMap R C π) * a + a ^ q := by
  rw [PowerSeries.subst_add ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha,
    ← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul ha, PowerSeries.subst_X ha,
    ← PowerSeries.smul_eq_C_mul, algebraMap_smul]

theorem nev_eq_sum {y : C} {N D : ℕ} (hy : y ^ N = 0) (hD : N ≤ D) (φ : PowerSeries R) :
    nev y φ = ∑ i ∈ Finset.range D, algebraMap R C (PowerSeries.coeff i φ) * y ^ i := by
  have hs := hasSubst_C (C := C) (y := y) ⟨N, hy⟩
  have h1 := PowerSeries.constantCoeff_subst (R := R) hs φ
  have h2 : ∀ d, MvPowerSeries.constantCoeff ((PowerSeries.C y : PowerSeries C) ^ d) = y ^ d := by
    intro d
    rw [map_pow]
    congr 1
  simp only [h2] at h1
  have h3 : nev y φ = ∑ᶠ d : ℕ, (PowerSeries.coeff d φ) • y ^ d := h1
  rw [h3, finsum_eq_sum_of_support_subset (s := Finset.range D)]
  · exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [pow_eq_zero_of_le (by omega) hy, smul_zero])

theorem nev_step {y : C} (hy : IsNilpotent y) (π : R) (q : ℕ) (hq : q ≠ 0) {φ : PowerSeries R}
    (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R)
      = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ) :
    nev (algebraMap R C π * y + y ^ q) φ = algebraMap R C π * nev y φ + nev y φ ^ q := by
  have hs := hasSubst_C (C := C) hy
  have hφ : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hf : PowerSeries.HasSubst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [hq]
  have e1 := PowerSeries.subst_comp_subst_apply (R := R) (S := R) (T := C) hφ hs
    (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R)
  have e2 := PowerSeries.subst_comp_subst_apply (R := R) (S := R) (T := C) hf hs φ
  rw [hc, e2] at e1
  have hΦ : PowerSeries.HasSubst (PowerSeries.subst (PowerSeries.C y : PowerSeries C) φ : PowerSeries C) := by
    have := PowerSeries.HasSubst.comp hφ hs
    rwa [PowerSeries.coe_substAlgHom] at this
  rw [subst_lt hs, subst_lt hΦ] at e1
  have e3 : (PowerSeries.C (algebraMap R C π) * PowerSeries.C y + PowerSeries.C y ^ q : PowerSeries C)
      = PowerSeries.C (algebraMap R C π * y + y ^ q) := by
    simp only [map_add, map_mul, map_pow]
  rw [e3] at e1
  have e4 := congrArg (PowerSeries.constantCoeff (R := C)) e1
  simpa [nev] using e4

theorem nev_iter {y : C} (hy : IsNilpotent y) (π : R) (q : ℕ) (hq : q ≠ 0) {φ : PowerSeries R}
    (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R)
      = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ) (n : ℕ) :
    nev (ltIter (algebraMap R C π) q n y) φ = ltIter (algebraMap R C π) q n (nev y φ) := by
  induction n with
  | zero => simp [ltIter]
  | succ n ih =>
    rw [ltIter_succ, ltIter_succ, nev_step (nil_ltIter _ hq hy n) π q hq h0 hc, ih]

theorem nev_core {y u c s : C} (hy : IsNilpotent y) (π : R) (q : ℕ) (hq : q ≠ 0)
    (hqs : (q : C) = algebraMap R C π * s) {φ : PowerSeries R}
    (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R)
      = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ) (n : ℕ)
    (h1 : nev y φ - u = algebraMap R C π * c) (hw : algebraMap R C π ^ (n + 1) = 0) :
    nev (ltIter (algebraMap R C π) q n y) φ = ltIter (algebraMap R C π) q n u := by
  obtain ⟨d, hd⟩ := ltIter_congr _ s q hqs _ _ c h1 n
  rw [nev_iter hy π q hq h0 hc]
  rw [hw, zero_mul] at hd
  exact sub_eq_zero.1 hd

end Nil

section Main

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

theorem pow_mem_F (env : PerEnv S F ϖ) {x : B} (hx : x ∈ F 1) (k : ℕ) : x ^ k ∈ F k := by
  induction k with
  | zero => simp [env.top]
  | succ k ih => rw [pow_succ]; exact env.mul_le k 1 (Ideal.mul_mem_mul ih hx)

theorem exists_near_ideal (hϖ : ϖ ∈ S) (J : Ideal B) (m : ℕ) :
    ∃ I : Ideal S, ∀ x : S, x ∈ I ↔ Near S ϖ J m (x : B) := by
  refine ⟨Ideal.span {(⟨ϖ, hϖ⟩ : S) ^ m} ⊔ J.comap S.subtype, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine ⟨c, c.2, ?_⟩
    have hb' : (b : B) ∈ J := hb
    have e : (((c * (⟨ϖ, hϖ⟩ : S) ^ m + b : S)) : B) - ϖ ^ m * c = b := by
      push_cast; ring
    rwa [e]
  · rintro ⟨s, hs, hx⟩
    have e : x = (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m + (x - (⟨ϖ, hϖ⟩ : S) ^ m * ⟨s, hs⟩) := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))) ?_
    refine Ideal.mem_sup_right ?_
    show (((x - (⟨ϖ, hϖ⟩ : S) ^ m * ⟨s, hs⟩ : S)) : B) ∈ J
    push_cast
    exact hx

theorem finiteRing_sq_sub_mul_sq_eq_of_card {R C : Type} [CommRing R] [CommRing C] [Algebra R C] (env : PerEnv S F ϖ) (k m : ℕ) (mk : S →+* C)
    (hnear : ∀ x : S, mk x = 0 ↔ Near S ϖ (F k) m (x : B)) (h : R →+* B) (h' : R →+* S)
    (hh : ∀ c, (h' c : B) = h c) (hmk : ∀ c, mk (h' c) = algebraMap R C c)
    (π : R) (hπ : h π = ϖ) (q : ℕ) (hq2 : 2 ≤ q) (s : B) (hsS : s ∈ S) (hs : (q : B) = ϖ * s)
    (φ : PowerSeries R) (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R)
      = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ)
    (σ : B →+* B) (hσS : ∀ s ∈ S, σ s ∈ S) (hσϖ : σ ϖ = ϖ)
    (v : ℕ → B) (hvS : ∀ n, v n ∈ S) (hv : ∀ n, v (n + 1) ^ q = v n)
    (M : ℕ) (s0 : B) (hs0 : s0 ∈ S) (hf0 : v 0 ^ M - ϖ ^ 1 * s0 ∈ F 1)
    (Q : B) (hQS : Q ∈ S) (hQ : ∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a)
    (hE : ∀ n, EvalMod S F ϖ h φ (v n) (σ (v n)) 1) :
    ∃ D, ∀ D' ≥ D, Near S ϖ (F k) m
      ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * Q ^ i) - σ Q) := by
  have hq0 : q ≠ 0 := by omega
  obtain ⟨ϖ', hϖ'⟩ : ∃ x : S, (x : B) = ϖ := ⟨⟨ϖ, env.mem⟩, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ x : ℕ → S, ∀ n, (x n : B) = v n := ⟨fun n => ⟨v n, hvS n⟩, fun _ => rfl⟩
  obtain ⟨s', hs'⟩ : ∃ x : S, (x : B) = s := ⟨⟨s, hsS⟩, rfl⟩
  obtain ⟨s0', hs0'⟩ : ∃ x : S, (x : B) = s0 := ⟨⟨s0, hs0⟩, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ x : S, (x : B) = Q := ⟨⟨Q, hQS⟩, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ x : S, (x : B) = σ Q := ⟨⟨σ Q, hσS _ hQS⟩, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ x : S, (x : B) = σ (v m) := ⟨⟨σ (v m), hσS _ (hvS m)⟩, rfl⟩
  have hπ' : h' π = ϖ' := Subtype.ext ((hh π).trans (hπ.trans hϖ'.symm))
  have hw : algebraMap R C π = mk ϖ' := by rw [← hmk, hπ']
  have hmF : ∀ x : S, (x : B) ∈ F k → mk x = 0 := fun x hx =>
    (hnear x).2 ⟨0, S.zero_mem, by simpa using hx⟩
  have hwm : mk ϖ' ^ m = 0 := by
    rw [← map_pow]
    refine (hnear _).2 ⟨1, S.one_mem, ?_⟩
    simp [hϖ']
  have hwm1 : mk ϖ' ^ (m + 1) = 0 := by rw [pow_succ, hwm, zero_mul]
  have hn0 : IsNilpotent (mk (v' 0)) := by
    have hf : ((v' 0 ^ M - ϖ' ^ 1 * s0' : S) : B) ∈ F 1 := by
      push_cast
      rw [hv', hϖ', hs0']
      exact hf0
    have hfk : mk (v' 0 ^ M - ϖ' ^ 1 * s0') ^ k = 0 := by
      rw [← map_pow]
      refine hmF _ ?_
      rw [SubmonoidClass.coe_pow]
      exact pow_mem_F env hf k
    have e : mk (v' 0) ^ M = mk (v' 0 ^ M - ϖ' ^ 1 * s0') + mk ϖ' * mk s0' := by
      simp only [map_sub, map_mul, map_pow, pow_one]
      ring
    have hnil : IsNilpotent (mk (v' 0) ^ M) := by
      rw [e, ← mem_nilradical]
      exact add_mem (mem_nilradical.2 ⟨k, hfk⟩) (Ideal.mul_mem_right _ _ (mem_nilradical.2 ⟨m, hwm⟩))
    obtain ⟨e', he⟩ := hnil
    exact ⟨M * e', by rw [pow_mul, he]⟩
  have hn : ∀ n, IsNilpotent (mk (v' n)) := by
    intro n
    induction n with
    | zero => exact hn0
    | succ n ih =>
      obtain ⟨e', he⟩ := ih
      have e : mk (v' (n + 1)) ^ q = mk (v' n) := by
        rw [← map_pow]
        congr 1
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, hv', hv', hv n]
      exact ⟨q * e', by rw [pow_mul, e, he]⟩
  have hsum : ∀ (y : S) (D : ℕ), ((∑ i ∈ Finset.range D, h' (PowerSeries.coeff i φ) * y ^ i : S) : B)
      = ∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * (y : B) ^ i := by
    intro y D
    simp [hh]
  have hmsum : ∀ (y : S) {N D : ℕ}, mk y ^ N = 0 → N ≤ D →
      mk (∑ i ∈ Finset.range D, h' (PowerSeries.coeff i φ) * y ^ i) = nev (mk y) φ := by
    intro y N D hN hD
    rw [nev_eq_sum hN hD]
    simp [map_sum, hmk]
  obtain ⟨N, hN⟩ := hn m
  obtain ⟨D0, hD0⟩ := hE m k
  obtain ⟨c, hcS, hcF⟩ := hD0 (max D0 N) (le_max_left _ _)
  obtain ⟨c', hc'⟩ : ∃ x : S, (x : B) = c := ⟨⟨c, hcS⟩, rfl⟩
  have h1 : nev (mk (v' m)) φ - mk u' = algebraMap R C π * mk c' := by
    rw [← hmsum (v' m) hN (le_max_right D0 N), hw]
    have e := hmF ((∑ i ∈ Finset.range (max D0 N), h' (PowerSeries.coeff i φ) * v' m ^ i) - u' - ϖ' ^ 1 * c') (by
      rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, hsum, hv', hu']
      push_cast
      rw [hϖ', hc']
      exact hcF)
    rw [map_sub, map_sub, map_mul, map_pow, pow_one] at e
    linear_combination e
  have hqs : (q : C) = algebraMap R C π * mk s' := by
    rw [hw, ← map_mul, ← map_natCast mk q]
    congr 1
    apply Subtype.ext
    push_cast
    rw [hϖ', hs', hs]
  have key := nev_core (hn m) π q hq0 hqs h0 hc m h1 (by rw [hw]; exact hwm1)
  obtain ⟨a, haS, hQa⟩ := hQ m
  obtain ⟨a', ha'⟩ : ∃ x : S, (x : B) = a := ⟨⟨a, haS⟩, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ x : S, (x : B) = σ a := ⟨⟨σ a, hσS _ haS⟩, rfl⟩
  have hcoe : ∀ x : S, ((ltIter ϖ' q m x : S) : B) = ltIter ϖ q m (x : B) := fun x => by
    have := map_ltIter S.subtype ϖ' q m x
    simpa [hϖ'] using this
  have e1 : mk Q' = ltIter (algebraMap R C π) q m (mk (v' m)) := by
    have e : Q' = ltIter ϖ' q m (v' m) + ϖ' ^ (m + 1) * a' := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, hcoe]
      push_cast
      rw [hQ', hv', hϖ', ha']
      linear_combination hQa
    rw [e, map_add, map_mul, map_pow, hwm1, zero_mul, add_zero, map_ltIter, hw]
  have e2 : mk R' = ltIter (algebraMap R C π) q m (mk u') := by
    have e : R' = ltIter ϖ' q m u' + ϖ' ^ (m + 1) * b' := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, hcoe]
      push_cast
      rw [hR', hu', hϖ', hb']
      have e3 : σ (ltIter ϖ q m (v m)) = ltIter ϖ q m (σ (v m)) := by rw [map_ltIter, hσϖ]
      have e4 := congrArg σ hQa
      rw [map_sub, map_mul, map_pow, hσϖ, e3] at e4
      linear_combination e4
    rw [e, map_add, map_mul, map_pow, hwm1, zero_mul, add_zero, map_ltIter, hw]
  have hfin : nev (mk Q') φ = mk R' := by rw [e1, e2]; exact key
  have hnQ : IsNilpotent (mk Q') := by rw [e1]; exact nil_ltIter _ hq0 (hn m) m
  obtain ⟨N2, hN2⟩ := hnQ
  refine ⟨N2, fun D' hD' => ?_⟩
  have hfinal := (hnear ((∑ i ∈ Finset.range D', h' (PowerSeries.coeff i φ) * Q' ^ i) - R')).1
    (by rw [map_sub, hmsum Q' hN2 hD', hfin, sub_self])
  rwa [AddSubgroupClass.coe_sub, hsum, hQ', hR'] at hfinal

end Main

end GlobalTheory.CompanionTheory.LTPer.QGal

theorem GlobalTheory.CompanionTheory.LTPer.evalMod_sigma_of_congr : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {R : Type} [CommRing R], PerEnv S F ϖ →
    ∀ (h : R →+* B), (∀ c, h c ∈ S) → ∀ (π : R), h π = ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ →
    ∀ (σ : B →+* B), (∀ s ∈ S, σ s ∈ S) → (∀ k, ∀ x ∈ F k, σ x ∈ F k) → σ ϖ = ϖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → (∀ n, v (n + 1) ^ q = v n) →
      (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (v 0 ^ M)) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) →
      (∀ n, EvalMod S F ϖ h φ (v n) (σ (v n)) 1) → ∀ m, EvalMod S F ϖ h φ Q (σ Q) m := by
  intro B _ S F ϖ R _ env h hS π hπ q hq2 hqs φ h0 hc σ hσS _ hσϖ v hvS hv hM Q hQS hQ hE m k
  obtain ⟨s, hsS, hs⟩ := hqs
  obtain ⟨M, _, s0, hs0, hf0⟩ := hM
  obtain ⟨I, hI⟩ := GlobalTheory.CompanionTheory.LTPer.QGal.exists_near_ideal (S := S) env.mem (F k) m
  obtain ⟨h', hh⟩ : ∃ h' : R →+* S, ∀ c, (h' c : B) = h c := ⟨h.codRestrict S hS, fun _ => rfl⟩
  letI : Algebra R (S ⧸ I) := ((Ideal.Quotient.mk I).comp h').toAlgebra
  exact GlobalTheory.CompanionTheory.LTPer.QGal.finiteRing_sq_sub_mul_sq_eq_of_card env k m (Ideal.Quotient.mk I)
    (fun x => Ideal.Quotient.eq_zero_iff_mem.trans (hI x)) h h' hh (fun _ => rfl) π hπ q hq2 s hsS hs φ h0 hc
    σ hσS hσϖ v hvS hv M s0 hs0 hf0 Q hQS hQ hE
