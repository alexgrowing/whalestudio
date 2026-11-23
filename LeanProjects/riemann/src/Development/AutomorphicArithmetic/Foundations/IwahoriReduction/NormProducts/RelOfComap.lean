import Mathlib
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial UniqueFactorizationMonoid
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.Ns

section core

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L]

private def Rel (m : ℕ) (I J : Ideal B) : Prop :=
  ∃ (x y : B) (E F : Ideal B), x ≠ 0 ∧ y ≠ 0 ∧ E ≠ 0 ∧ F ≠ 0 ∧
    Algebra.norm K (algebraMap B L x) = Algebra.norm K (algebraMap B L y) ∧
    Ideal.span {x} * I * E ^ m = Ideal.span {y} * J * F ^ m

private theorem rel_mul {m : ℕ} {I J I' J' : Ideal B} (h : Rel K L m I J) (h' : Rel K L m I' J') :
    Rel K L m (I * I') (J * J') := by
  obtain ⟨x, y, E, F, hx, hy, hE, hF, hn, he⟩ := h
  obtain ⟨x', y', E', F', hx', hy', hE', hF', hn', he'⟩ := h'
  refine ⟨x * x', y * y', E * E', F * F', mul_ne_zero hx hx', mul_ne_zero hy hy',
    mul_ne_zero hE hE', mul_ne_zero hF hF', by simp only [map_mul, hn, hn'], ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  calc _ = (Ideal.span {x} * I * E ^ m) * (Ideal.span {x'} * I' * E' ^ m) := by ring
    _ = _ := by rw [he, he']; ring

private theorem rel_prod {m : ℕ} (φ : Ideal B → Ideal B) (s : Multiset (Ideal B))
    (h : ∀ P ∈ s, Rel K L m P (φ P)) : Rel K L m s.prod (s.map φ).prod := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, 1, 1, 1, one_ne_zero, one_ne_zero, one_ne_zero, one_ne_zero, rfl, rfl⟩
  | cons a s ih =>
    simp only [Multiset.prod_cons, Multiset.map_cons]
    exact rel_mul K L (h a (Multiset.mem_cons_self a s))
      (ih fun P hP => h P (Multiset.mem_cons_of_mem hP))

private theorem rel_of_comap {m : ℕ} (hC : ∀ c : ClassGroup B, ∃ d, c = d ^ m) {P Q : Ideal B}
    (hP : P ≠ 0) (σ : Gal(L/K)) (h : Ideal.comap (galRestrict A K L B σ) P = Q) :
    Rel K L m P Q := by
  classical
  set τ := galRestrict A K L B σ with hτ
  let e : B ≃+* B := τ.symm.toRingEquiv
  have hτe : ∀ x, τ (e x) = x := fun x => τ.apply_symm_apply x
  have hnm : ∀ x, Algebra.norm K (algebraMap B L (e x)) = Algebra.norm K (algebraMap B L x) := by
    intro x
    conv_rhs => rw [← hτe x]
    rw [hτ, algebraMap_galRestrict_apply]
    exact (Algebra.norm_eq_of_algEquiv σ _).symm
  have hQ : Q = P.map e := by
    rw [← h]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      exact ⟨τ x, hx, τ.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hτe]
      exact hy
  have hP' : P ∈ nonZeroDivisors (Ideal B) := mem_nonZeroDivisors_of_ne_zero hP
  obtain ⟨d, hd⟩ := hC (ClassGroup.mk0 ⟨P, hP'⟩)
  obtain ⟨E0, rfl⟩ := ClassGroup.mk0_surjective d
  rw [← map_pow, ClassGroup.mk0_eq_mk0_iff] at hd
  obtain ⟨x, y, hx, hy, hxy⟩ := hd
  have hE : (E0 : Ideal B) ≠ 0 := nonZeroDivisors.coe_ne_zero E0
  simp only [SubmonoidClass.coe_pow] at hxy
  have h2 := congrArg (Ideal.map e) hxy
  simp only [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton, ← hQ] at h2
  have hne : ∀ z : B, z ≠ 0 → e z ≠ 0 := fun z hz => (map_ne_zero_iff e e.injective).2 hz
  have heE : (E0 : Ideal B).map e ≠ 0 := by
    intro h0
    apply hE
    exact (Ideal.map_eq_bot_iff_of_injective e.injective).1 h0
  refine ⟨x * e y, y * e x, (E0 : Ideal B).map e, E0, mul_ne_zero hx (hne y hy),
    mul_ne_zero hy (hne x hx), heE, hE, by simp only [map_mul, hnm, mul_comm], ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  calc _ = Ideal.span {e y} * (Ideal.span {x} * P) * ((E0 : Ideal B).map e) ^ m := by ring
    _ = Ideal.span {y} * (Ideal.span {e y} * ((E0 : Ideal B).map e) ^ m) * (E0 : Ideal B) ^ m := by
        rw [hxy]; ring
    _ = _ := by rw [← h2]; ring

end core

section core2

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Module.Finite A B] [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)]

private theorem inertia_one (hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P)
    (P : Ideal B) [hP : P.IsMaximal] [(P.under A).IsMaximal] : P.inertiaDeg A = 1 := by
  letI : Field (A ⧸ P.under A) := Ideal.Quotient.field _
  have h1 : Module.finrank (A ⧸ P.under A) (B ⧸ P) = 1 := by
    refine (finrank_eq_one_iff_of_nonzero' (1 : B ⧸ P) one_ne_zero).2 fun w => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨a, ha⟩ := hres P hP b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Algebra.smul_def, mul_one]
    exact (Ideal.Quotient.eq.2 ha).symm
  rw [← h1]
  have hl : P.LiesOver (P.under A) := ⟨rfl⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (P.under A) P]

open Classical in
private theorem core {m : ℕ} (hC : ∀ c : ClassGroup B, ∃ d, c = d ^ m)
    (hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P)
    (g : B) (hg : g ≠ 0)
    (hdiv : ∀ p : Ideal A, m ∣ Multiset.count p (normalizedFactors (Ideal.span {Algebra.intNorm A B g}))) :
    ∃ D : Ideal B, Rel K L m (Ideal.span {g}) (D ^ m) := by
  have hI : Ideal.span {g} ≠ ⊥ := by simpa using hg
  set s := normalizedFactors (Ideal.span {g}) with hs
  have hsP : ∀ P ∈ s, P.IsPrime ∧ P ≠ 0 := fun P hP =>
    ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P hP),
      (prime_of_normalized_factor P hP).ne_zero⟩
  have hsM : ∀ P ∈ s, P.IsMaximal := fun P hP =>
    (hsP P hP).1.isMaximal (hsP P hP).2
  let un : Ideal B → Ideal A := fun P => P.under A
  let S : Set (Ideal B) := {P | P.IsPrime ∧ P ≠ 0}
  let ch : Ideal A → Ideal B := Function.invFunOn un S
  have hunM : ∀ P ∈ s, (un P).IsMaximal ∧ un P ≠ 0 := fun P hP => by
    have := hsM P hP
    refine ⟨Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P, fun h0 => (hsP P hP).2 ?_⟩
    exact Ideal.eq_bot_of_comap_eq_bot h0
  have hch : ∀ P ∈ s, ch (un P) ∈ S ∧ un (ch (un P)) = un P := fun P hP =>
    Function.invFunOn_pos ⟨P, hsP P hP, rfl⟩
  have hrel : ∀ P ∈ s, Rel K L m P (ch (un P)) := by
    intro P hP
    obtain ⟨⟨hQp, hQ0⟩, hQu⟩ := hch P hP
    have := (hsP P hP).1
    have h1 : P ∈ (un P).primesOver B := ⟨(hsP P hP).1, ⟨rfl⟩⟩
    have h2 : ch (un P) ∈ (un P).primesOver B := ⟨hQp, ⟨hQu.symm⟩⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq A K L B h1 h2
    exact rel_of_comap K L hC (hsP P hP).2 σ hσ
  have hR := rel_prod K L (fun P => ch (un P)) s hrel
  rw [hs, Ideal.prod_normalizedFactors_eq_self hI, ← hs] at hR
  set t := s.map un with ht
  have hnorm : Ideal.span {Algebra.intNorm A B g} = t.prod := by
    rw [← Ideal.relNorm_singleton, ← Ideal.prod_normalizedFactors_eq_self hI, ← hs,
      map_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun P hP => ?_
    have := hsM P hP
    have := (hunM P hP).1
    have hl : P.LiesOver (P.under A) := ⟨rfl⟩
    rw [Ideal.relNorm_eq_pow_of_isMaximal P (P.under A), inertia_one hres P, pow_one]
  have hfac : normalizedFactors t.prod = t := by
    refine normalizedFactors_prod_of_prime fun p hp => ?_
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hp
    exact Ideal.prime_of_isPrime (hunM P hP).2 (hunM P hP).1.isPrime
  obtain ⟨T, hT⟩ := Multiset.exists_smul_of_dvd_count t (k := m) fun p _ => by
    have := hdiv p
    rwa [hnorm, hfac] at this
  refine ⟨(T.map ch).prod, ?_⟩
  have hm : s.map (fun P => ch (un P)) = m • T.map ch := by
    rw [← Multiset.map_nsmul, ← hT, ht, Multiset.map_map]
    rfl
  rwa [hm, Multiset.prod_nsmul] at hR

end core2

section fin

variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L]

private theorem principal_in (W : ValuationSubring L) (φ : B →+* W) (hφ : Function.Injective φ)
    (E : Ideal B) (hE : E ≠ 0) : ∃ w : W, w ≠ 0 ∧ E.map φ = Ideal.span {w} := by
  have hfg : (E.map φ).FG := Ideal.FG.map (IsNoetherian.noetherian E) φ
  obtain ⟨w, hw⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
  refine ⟨w, ?_, by simpa using hw⟩
  rintro rfl
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
  have h1 : φ b ∈ E.map φ := Ideal.mem_map_of_mem φ hb
  rw [hw] at h1
  simp only [Submodule.span_zero_singleton, Submodule.mem_bot] at h1
  exact hb0 (hφ (h1.trans (map_zero φ).symm))

private theorem val_of {m : ℕ} (hm : 0 < m) (hinj : Function.Injective (algebraMap B L))
    (W : ValuationSubring L) (hW : ∀ b : B, algebraMap B L b ∈ W) {a y : B} {D E F : Ideal B}
    (ha : a ≠ 0) (hy : y ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0)
    (h : Ideal.span {a} * E ^ m = Ideal.span {y} * D ^ m * F ^ m) :
    ∃ c : L, c ≠ 0 ∧ W.valuation (algebraMap B L a / algebraMap B L y / c ^ m) = 1 := by
  let φ : B →+* W := (algebraMap B L).codRestrict W.toSubring hW
  have hcoe : ∀ b, ((φ b : W) : L) = algebraMap B L b := fun _ => rfl
  have hφ : Function.Injective φ := fun x y hxy => hinj (by rw [← hcoe, ← hcoe, hxy])
  have hD : D ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', mul_zero, zero_mul] at h
    exact mul_ne_zero (by simpa using ha) (pow_ne_zero m hE) h
  obtain ⟨e, he0, he⟩ := principal_in W φ hφ E hE
  obtain ⟨d, hd0, hd⟩ := principal_in W φ hφ D hD
  obtain ⟨f, hf0, hf⟩ := principal_in W φ hφ F hF
  have h2 := congrArg (Ideal.map φ) h
  simp only [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton, he, hd, hf,
    Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton] at h2
  rw [Ideal.span_singleton_eq_span_singleton] at h2
  obtain ⟨u, hu⟩ := h2
  have hL := congrArg (fun w : W => (w : L)) hu
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hcoe] at hL
  have he' : (e : L) ≠ 0 := by simpa using he0
  have hd' : (d : L) ≠ 0 := by simpa using hd0
  have hf' : (f : L) ≠ 0 := by simpa using hf0
  have hy' : algebraMap B L y ≠ 0 := fun h0 => hy (hinj (h0.trans (map_zero _).symm))
  refine ⟨d * f / e, div_ne_zero (mul_ne_zero hd' hf') he', ?_⟩
  have hz : algebraMap B L a / algebraMap B L y / ((d : L) * f / e) ^ m * ((u : W) : L) = 1 := by
    rw [div_pow, mul_pow]
    field_simp
    rw [hL]
  have h3 := congrArg W.valuation hz
  rw [map_mul, W.valuation_unit u, mul_one, map_one] at h3
  exact h3

end fin

section abs

open IsDedekindDomain

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Module.Finite A B] [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)] [IsFractionRing B L]

open Classical in
private theorem dvd_count {m : ℕ} (n : A) (hn : n ≠ 0) (h : ∀ v : HeightOneSpectrum A, ∃ z : K, z ≠ 0 ∧
      v.valuation K (algebraMap A K n) = (v.valuation K z) ^ m) (p : Ideal A) :
    m ∣ Multiset.count p (normalizedFactors (Ideal.span {n})) := by
  by_cases hp : p ∈ normalizedFactors (Ideal.span {n})
  · have hpr := prime_of_normalized_factor p hp
    let v : HeightOneSpectrum A := ⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩
    obtain ⟨z, hz0, hz⟩ := h v
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hn,
      Ideal.count_associates_factors_eq (by simpa using hn) v.isPrime v.ne_bot] at hz
    have h2 := congrArg WithZero.log hz
    rw [WithZero.log_exp, WithZero.log_pow] at h2
    have h3 : (m : ℤ) ∣ (Multiset.count p (normalizedFactors (Ideal.span {n})) : ℤ) :=
      ⟨-(v.valuation K z).log, by
        have : -(Multiset.count p (normalizedFactors (Ideal.span {n})) : ℤ) = m * (v.valuation K z).log := by
          simpa using h2
        linarith⟩
    exact Int.natCast_dvd_natCast.1 h3
  · rw [Multiset.count_eq_zero_of_notMem hp]
    exact dvd_zero m

private theorem abs_fin {m : ℕ} (hm : 0 < m) (hC : ∀ c : ClassGroup B, ∃ d, c = d ^ m)
    (hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P)
    (f : K) (hf0 : f ≠ 0) (g0 : L) (hg0 : Algebra.norm K g0 = f)
    (hf : ∀ v : HeightOneSpectrum A, ∃ c : K, c ≠ 0 ∧ v.valuation K (f / c ^ m) = 1) :
    ∃ f' : L, f' ≠ 0 ∧ Algebra.norm K f' = f ∧ ∀ W : ValuationSubring L,
      (∀ b : B, algebraMap B L b ∈ W) → ∃ c : L, c ≠ 0 ∧ W.valuation (f' / c ^ m) = 1 := by
  classical
  have hinj : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hg00 : g0 ≠ 0 := Algebra.norm_ne_zero_iff.1 (hg0 ▸ hf0)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) g0
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : algebraMap B L b ≠ 0 := fun h0 => hb0 (hinj (h0.trans (map_zero _).symm))
  have haL : algebraMap B L a ≠ 0 := fun h0 => hg00 (by rw [h0, zero_div])
  have ha0 : a ≠ 0 := fun h0 => haL (by rw [h0, map_zero])
  set g0 := algebraMap B L a / algebraMap B L b with hg0d
  set g := a * b ^ (m - 1) with hg
  have hg_ne : g ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hb0)
  have hgL : algebraMap B L g = g0 * algebraMap B L b ^ m := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hg, hg0d, map_mul, map_pow, Nat.add_sub_cancel]
    field_simp
    ring
  set n := Algebra.intNorm A B g with hn
  have hnK : algebraMap A K n = f * Algebra.norm K (algebraMap B L b) ^ m := by
    rw [hn, Algebra.algebraMap_intNorm (L := L), hgL, map_mul, map_pow, hg0]
  have hNb : Algebra.norm K (algebraMap B L b) ≠ 0 := Algebra.norm_ne_zero_iff.2 hbL
  have hn0 : n ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hnK
    exact mul_ne_zero hf0 (pow_ne_zero m hNb) hnK.symm
  have hdiv := dvd_count K (m := m) n hn0 (fun v => by
    obtain ⟨c, hc0, hc⟩ := hf v
    refine ⟨c * Algebra.norm K (algebraMap B L b), mul_ne_zero hc0 hNb, ?_⟩
    have hc' : v.valuation K f = v.valuation K c ^ m := by
      rw [map_div₀, map_pow] at hc
      exact (div_eq_one_iff_eq (pow_ne_zero m ((Valuation.ne_zero_iff _).2 hc0))).1 hc
    rw [hnK, map_mul, map_mul, map_pow, hc', mul_pow])
  obtain ⟨D, x, y, E, F, hx, hy, hE, hF, hxy, hR⟩ := core K L hC hres g hg_ne hdiv
  have hxL : algebraMap B L x ≠ 0 := fun h0 => hx (hinj (h0.trans (map_zero _).symm))
  have hyL : algebraMap B L y ≠ 0 := fun h0 => hy (hinj (h0.trans (map_zero _).symm))
  refine ⟨g0 * algebraMap B L x / algebraMap B L y, div_ne_zero (mul_ne_zero hg00 hxL) hyL, ?_, ?_⟩
  · have hNy : Algebra.norm K (algebraMap B L y) ≠ 0 := Algebra.norm_ne_zero_iff.2 hyL
    apply mul_right_cancel₀ hNy
    rw [← map_mul, div_mul_cancel₀ _ hyL, map_mul, hg0, hxy]
  · intro W hW
    rw [Ideal.span_singleton_mul_span_singleton] at hR
    obtain ⟨c, hc0, hc⟩ := val_of hm hinj W hW (mul_ne_zero hx hg_ne) hy hE hF hR
    refine ⟨c / algebraMap B L b, div_ne_zero hc0 hbL, ?_⟩
    rw [← hc, map_mul, hgL, div_pow]
    congr 1
    field_simp

end abs

private theorem mem_of_int {R L : Type*} [CommRing R] [Field L] [Algebra R L] (W : ValuationSubring L)
    (hW : ∀ p : R, algebraMap R L p ∈ W) {x : L} (hx : IsIntegral R x) : x ∈ W := by
  let ψ : R →+* W := (algebraMap R L).codRestrict W.toSubring hW
  obtain ⟨P, hP, h0⟩ := hx
  have h1 : IsIntegral W x := ⟨P.map ψ, hP.map ψ, by rw [eval₂_map]; exact h0⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact y.2

private theorem res_of (k B : Type*) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (P : Ideal B) (hP : P.IsMaximal) (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ P := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ P)).2
    (Ideal.Quotient.mk P b)
  exact ⟨c, Ideal.Quotient.eq.1 hc.symm⟩

end UpperTheory.Kd.K4.Ns

open UpperTheory.Kd.K4.Ns in
theorem UpperTheory.Kd.K4.nsAbs :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (K' : Type) [Field K'] [Algebra K K'] [Algebra k[X] K'] [IsScalarTower k[X] K K'] [FiniteDimensional K K'] [IsGalois K K'] (m : ℕ) (f : K), 0 < m → f ≠ 0 →
      (∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) →
      ∃ f' : K', f' ≠ 0 ∧ Algebra.norm K f' = f ∧
        ∀ B : ValuationSubring K', (∀ p : k[X], algebraMap k[X] K' p ∈ B) → ∃ c : K', c ≠ 0 ∧ B.valuation (f' / c ^ m) = 1 := by
  intro k K _ _ _ _ _ _ _ _ K' _ _ _ _ _ _ m f hm hf0 hf
  letI : Algebra (RatFunc k) K' := ((algebraMap K K').comp (algebraMap (RatFunc k) K)).toAlgebra
  haveI : IsScalarTower (RatFunc k) K K' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k[X] (RatFunc k) K' := .of_algebraMap_eq fun p => by
    rw [IsScalarTower.algebraMap_apply k[X] K K', IsScalarTower.algebraMap_apply k[X] (RatFunc k) K]
    rfl
  haveI : FiniteDimensional (RatFunc k) K' := .trans (RatFunc k) K K'
  haveI : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (RatFunc k) K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.IsTorsionFree k[X] K' := .trans_faithfulSMul k[X] (RatFunc k) K'
  let A := FunctionField.ringOfIntegers k K
  let B := FunctionField.ringOfIntegers k K'
  haveI : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K' _
  haveI : IsFractionRing A K := IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) K _
  haveI : IsFractionRing B K' := IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) K' _
  have hAB : ∀ a : A, algebraMap K K' (algebraMap A K a) ∈ B := fun a =>
    IsIntegral.algebraMap (R := k[X]) (A := K) (B := K') a.2
  letI : Algebra A B := (((algebraMap K K').comp (algebraMap A K)).codRestrict B hAB).toAlgebra
  haveI : IsScalarTower A K K' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A B K' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k[X] A K' := .of_algebraMap_eq fun p =>
    IsScalarTower.algebraMap_apply k[X] K K' p
  haveI : Algebra.IsIntegral k[X] A := inferInstanceAs (Algebra.IsIntegral k[X] (integralClosure k[X] K))
  have hinjB : Function.Injective (algebraMap B K') := IsFractionRing.injective B K'
  haveI : IsIntegralClosure B A K' := ⟨hinjB, fun {x} =>
    ⟨fun hx => ⟨⟨x, isIntegral_trans (R := k[X]) (A := A) x hx⟩, rfl⟩, by
      rintro ⟨b, rfl⟩
      exact IsIntegral.tower_top (R := k[X]) (A := A) b.2⟩⟩
  haveI : Module.Finite A B := IsIntegralClosure.finite A K K' B
  have hinjAB : Function.Injective (algebraMap A B) := fun x y hxy => by
    apply IsFractionRing.injective A K
    apply (algebraMap K K').injective
    exact congrArg (fun b : B => (b : K')) hxy
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinjAB
  haveI : Module.IsTorsionFree A B := inferInstance
  haveI : CharZero (FractionRing A) :=
    charZero_of_injective_ringHom (f := ((algebraMap A (FractionRing A)).comp (algebraMap k[X] A)).comp
      (algebraMap k k[X])) (RingHom.injective _)
  letI : Algebra k B := ((algebraMap k[X] B).comp (algebraMap k k[X])).toAlgebra
  haveI : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite k[X] B := IsIntegralClosure.finite k[X] (RatFunc k) K' _
  haveI : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  have hres : ∀ P : Ideal B, P.IsMaximal → ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ P := by
    intro P hP b
    obtain ⟨c, hc⟩ := res_of k B P hP b
    refine ⟨algebraMap k[X] A (algebraMap k k[X] c), ?_⟩
    convert hc using 2
    exact Subtype.ext (IsScalarTower.algebraMap_apply k[X] K K' _).symm
  have hfv : ∀ v : IsDedekindDomain.HeightOneSpectrum A, ∃ c : K, c ≠ 0 ∧ v.valuation K (f / c ^ m) = 1 := by
    intro v
    obtain ⟨c, hc0, hc⟩ := hf (v.valuation K).valuationSubring fun p =>
      (Valuation.mem_valuationSubring_iff _ _).2 (v.valuation_le_one (algebraMap k[X] A p))
    exact ⟨c, hc0, ((v.valuation K).isEquiv_valuation_valuationSubring.eq_one_iff_eq_one).2 hc⟩
  obtain ⟨g0, hg0⟩ := GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K K' (GlobalTheory.T.tsen_theorem k K) f hf0
  obtain ⟨f', h0, h1, h2⟩ := abs_fin (A := A) (B := B) K K' hm (fun c => GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K' m hm c)
    hres f hf0 g0 hg0 hfv
  exact ⟨f', h0, h1, fun W hW => h2 W fun b => mem_of_int W hW b.2⟩
