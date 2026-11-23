import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.LogGal

section Trunc

variable {R A : Type} [CommRing R] [CommRing A]

def tev (g : R →+* A) (y : A) (D : ℕ) (ψ : PowerSeries R) : A :=
  ∑ i ∈ Finset.range D, g (PowerSeries.coeff i ψ) * y ^ i

theorem tev_eq_eval₂ (g : R →+* A) (y : A) (D : ℕ) (ψ : PowerSeries R) :
    tev g y D ψ = (PowerSeries.trunc D ψ).eval₂ g y :=
  (PowerSeries.eval₂_trunc_eq_sum_range y g D ψ).symm

theorem tev_coe {g : R →+* A} {y : A} {D : ℕ} (hy : y ^ D = 0) (p : Polynomial R) :
    tev g y D (p : PowerSeries R) = p.eval₂ g y := by
  rw [tev_eq_eval₂]
  obtain ⟨r, hr⟩ : (Polynomial.X : Polynomial R) ^ D ∣
      p - PowerSeries.trunc D (p : PowerSeries R) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    simp [PowerSeries.coeff_trunc, hd]
  have hp : p = PowerSeries.trunc D (p : PowerSeries R) + Polynomial.X ^ D * r := by
    rw [← hr]; ring
  conv_rhs => rw [hp]
  simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, hy]

theorem tev_mul {g : R →+* A} {y : A} {D : ℕ} (hy : y ^ D = 0) (a b : PowerSeries R) :
    tev g y D (a * b) = tev g y D a * tev g y D b := by
  have h1 : tev g y D (a * b) =
      tev g y D ((PowerSeries.trunc D a * PowerSeries.trunc D b : Polynomial R) : PowerSeries R) := by
    rw [tev_eq_eval₂, tev_eq_eval₂, ← PowerSeries.trunc_trunc_mul_trunc]
    simp
  rw [h1, tev_coe hy, Polynomial.eval₂_mul, tev_eq_eval₂, tev_eq_eval₂]

def tevHom (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) : PowerSeries R →+* A where
  toFun := tev g y D
  map_one' := by simpa using tev_coe (g := g) hy 1
  map_mul' := tev_mul hy
  map_zero' := by simp [tev]
  map_add' a b := by simp [tev, add_mul, Finset.sum_add_distrib]

theorem tevHom_apply (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) (ψ : PowerSeries R) :
    tevHom g y D hy ψ = tev g y D ψ := rfl

theorem tevHom_C (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) (c : R) :
    tevHom g y D hy (PowerSeries.C c) = g c := by
  simpa [tevHom_apply] using tev_coe (g := g) hy (Polynomial.C c)

theorem tevHom_X (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) :
    tevHom g y D hy PowerSeries.X = y := by
  simpa [tevHom_apply] using tev_coe (g := g) hy Polynomial.X

theorem lt_pow_zero {y c : A} {q D : ℕ} (hq : 2 ≤ q) (hy : y ^ D = 0) : (c * y + y ^ q) ^ D = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, q = e + 1 := ⟨q - 1, by omega⟩
  have : c * y + y ^ (e + 1) = y * (c + y ^ e) := by ring
  rw [this, mul_pow, hy, zero_mul]

theorem tev_comm (g : R →+* A) (π : R) {q : ℕ} (hq : 2 ≤ q) (φ : PowerSeries R)
    (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ)
    {y : A} {D : ℕ} (hy : y ^ D = 0) :
    tev g (g π * y + y ^ q) D φ = g π * tev g y D φ + tev g y D φ ^ q := by
  set f : PowerSeries R := PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q with hf
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    have : q ≠ 0 := by omega
    simp [hf, this]
  have hfS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hφS : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hy' : (g π * y + y ^ q) ^ D = 0 := lt_pow_zero hq hy
  have h1 : tevHom g y D hy (PowerSeries.subst φ f) =
      g π * tevHom g y D hy φ + tevHom g y D hy φ ^ q := by
    have : (PowerSeries.subst φ f : PowerSeries R) = PowerSeries.C π * φ + φ ^ q := by
      rw [hf, PowerSeries.subst_add hφS, PowerSeries.subst_mul hφS, PowerSeries.subst_pow hφS,
        PowerSeries.subst_X hφS, PowerSeries.subst_C]
      rfl
    rw [this, map_add, map_mul, map_pow, tevHom_C]
  let Θ : PowerSeries R →+* A :=
    (tevHom g y D hy).comp
      (PowerSeries.substAlgHom (R := R) (S := R) (τ := Unit) hfS).toRingHom
  have hΘ : ∀ ψ, Θ ψ = tevHom g y D hy (PowerSeries.subst f ψ) := by
    intro ψ
    simp only [Θ, RingHom.comp_apply]
    exact congrArg _ (congrFun (PowerSeries.coe_substAlgHom hfS) ψ)
  have hΘX : Θ PowerSeries.X = g π * y + y ^ q := by
    rw [hΘ, PowerSeries.subst_X hfS, hf, map_add, map_mul, map_pow, tevHom_C, tevHom_X]
  have hpoly : ∀ p : Polynomial R, Θ (p : PowerSeries R) =
      tevHom g (g π * y + y ^ q) D hy' (p : PowerSeries R) := by
    intro p
    have : Θ.comp (Polynomial.coeToPowerSeries.ringHom) =
        (tevHom g (g π * y + y ^ q) D hy').comp (Polynomial.coeToPowerSeries.ringHom) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
        rw [hΘ, PowerSeries.subst_C, tevHom_C]
        exact tevHom_C g y D hy a
      · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
        rw [hΘX, tevHom_X]
    exact congrArg (fun u => u p) (congrArg DFunLike.coe this)
  obtain ⟨ρ, hρ⟩ : (PowerSeries.X : PowerSeries R) ^ D ∣
      φ - (PowerSeries.trunc D φ : PowerSeries R) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    simp [PowerSeries.coeff_trunc, hd]
  have hφ : φ = (PowerSeries.trunc D φ : PowerSeries R) + PowerSeries.X ^ D * ρ := by
    rw [← hρ]; ring
  have h2 : Θ φ = tevHom g (g π * y + y ^ q) D hy' φ := by
    rw [hφ, map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, hΘX, tevHom_X, hy', zero_mul,
      zero_mul]
  rw [← tevHom_apply g _ D hy', ← tevHom_apply g y D hy, ← h2, hΘ, ← hc, h1]

end Trunc

section Abs

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

theorem near_add {J : Ideal B} {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x + y) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨s', hs', hy⟩ := hy
  refine ⟨s + s', S.add_mem hs hs', ?_⟩
  have e : x + y - ϖ ^ m * (s + s') = (x - ϖ ^ m * s) + (y - ϖ ^ m * s') := by ring
  rw [e]
  exact J.add_mem hx hy

theorem near_sub {J : Ideal B} {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x - y) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨s', hs', hy⟩ := hy
  refine ⟨s - s', S.sub_mem hs hs', ?_⟩
  have e : x - y - ϖ ^ m * (s - s') = (x - ϖ ^ m * s) - (y - ϖ ^ m * s') := by ring
  rw [e]
  exact J.sub_mem hx hy

theorem near_mul {J : Ideal B} {m : ℕ} {x a : B} (ha : a ∈ S) (hx : Near S ϖ J m x) :
    Near S ϖ J m (a * x) := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨a * s, S.mul_mem ha hs, ?_⟩
  have e : a * x - ϖ ^ m * (a * s) = a * (x - ϖ ^ m * s) := by ring
  rw [e]
  exact J.mul_mem_left a hx

theorem near_map (σ : B →+* B) (hS : ∀ s ∈ S, σ s ∈ S) {J : Ideal B} (hJ : ∀ x ∈ J, σ x ∈ J)
    (hϖ : σ ϖ = ϖ) {m : ℕ} {x : B} (hx : Near S ϖ J m x) : Near S ϖ J m (σ x) := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨σ s, hS s hs, ?_⟩
  have := hJ _ hx
  rwa [map_sub, map_mul, map_pow, hϖ] at this

def nearI (S : Subring B) (F : ℕ → Ideal B) (hϖ : ϖ ∈ S) (k m : ℕ) : Ideal S :=
  Ideal.span {(⟨ϖ, hϖ⟩ : S) ^ m} ⊔ (F k).comap S.subtype

theorem mem_nearI (hϖ : ϖ ∈ S) {k m : ℕ} {x : S} :
    x ∈ nearI S F hϖ k m ↔ Near S ϖ (F k) m (x : B) := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine ⟨c, c.2, ?_⟩
    have hb' : ((b : S) : B) ∈ F k := hb
    have e : ((c * (⟨ϖ, hϖ⟩ : S) ^ m + b : S) : B) - ϖ ^ m * (c : B) = (b : B) := by
      push_cast
      ring
    rw [e]
    exact hb'
  · rintro ⟨s, hs, hx⟩
    refine Submodule.mem_sup.2 ⟨(⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m,
      Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m, ?_, by ring⟩
    have e : ((x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m : S) : B) = (x : B) - ϖ ^ m * s := by
      push_cast
      ring
    show ((x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m : S) : B) ∈ F k
    rw [e]
    exact hx

theorem pow_mem_F (E : PerEnv S F ϖ) {x : B} (hx : x ∈ F 1) (k : ℕ) : x ^ k ∈ F k := by
  induction k with
  | zero => rw [E.top]; exact Submodule.mem_top
  | succ k ih =>
    rw [pow_succ]
    exact E.mul_le k 1 (Ideal.mul_mem_mul ih hx)

theorem nilp_of_near (E : PerEnv S F ϖ) (Q : S) {M : ℕ} (hN : Near S ϖ (F 1) 1 ((Q : B) ^ M))
    (k m : ℕ) : IsNilpotent (Ideal.Quotient.mk (nearI S F E.mem k m) Q) := by
  obtain ⟨s, hs, hx⟩ := hN
  set I := nearI S F E.mem k m with hI
  let sS : S := ⟨s, hs⟩
  let wS : S := ⟨ϖ, E.mem⟩
  let xS : S := Q ^ M - wS ^ 1 * sS
  have hxS : (xS : B) ∈ F 1 := by
    have e : (xS : B) = (Q : B) ^ M - ϖ ^ 1 * s := by
      simp [xS, sS, wS]
    rw [e]
    exact hx
  have hw : IsNilpotent (Ideal.Quotient.mk I wS) := by
    refine ⟨m, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hxn : IsNilpotent (Ideal.Quotient.mk I xS) := by
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_right ?_
    show ((xS ^ k : S) : B) ∈ F k
    push_cast
    exact pow_mem_F E hxS k
  have hQ : Ideal.Quotient.mk I Q ^ M =
      Ideal.Quotient.mk I wS * Ideal.Quotient.mk I sS + Ideal.Quotient.mk I xS := by
    rw [← map_pow, ← map_mul, ← map_add]
    congr 1
    simp [xS]
  have : IsNilpotent (Ideal.Quotient.mk I Q ^ M) := by
    rw [hQ]
    exact (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_right hw) hxn
  exact IsNilpotent.of_pow this

theorem ltIter_succ (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q :=
  Function.iterate_succ_apply' _ _ _

theorem ltIter_mem (hϖ : ϖ ∈ S) (q n : ℕ) {x : B} (hx : x ∈ S) : ltIter ϖ q n x ∈ S := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [ltIter_succ]
    exact S.add_mem (S.mul_mem hϖ ih) (S.pow_mem ih q)

variable {R : Type} [CommRing R]

def gq (E : PerEnv S F ϖ) (h : R →+* B) (hh : ∀ c, h c ∈ S) (k m : ℕ) :
    R →+* S ⧸ nearI S F E.mem k m :=
  (Ideal.Quotient.mk _).comp (h.codRestrict S hh)

theorem tev_gq (E : PerEnv S F ϖ) (h : R →+* B) (hh : ∀ c, h c ∈ S) (k m D : ℕ)
    (φ : PowerSeries R) (y : S) :
    ∃ p : S, (p : B) = ∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * (y : B) ^ i ∧
      tev (gq E h hh k m) (Ideal.Quotient.mk _ y) D φ = Ideal.Quotient.mk _ p := by
  refine ⟨∑ i ∈ Finset.range D, (h.codRestrict S hh) (PowerSeries.coeff i φ) * y ^ i, ?_, ?_⟩
  · push_cast
    rfl
  · simp [tev, gq, map_sum]

theorem iter_val (E : PerEnv S F ϖ) (h : R →+* B) (hh : ∀ c, h c ∈ S) (π : R) (hπ : h π = ϖ)
    {q : ℕ} (hq : 2 ≤ q) (φ : PowerSeries R) (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ)
    (σ : B →+* B) (hσS : ∀ s ∈ S, σ s ∈ S) (hσϖ : σ ϖ = ϖ) (Q : S)
    (hnil : ∀ k m, IsNilpotent (Ideal.Quotient.mk (nearI S F E.mem k m) Q))
    (hev : ∀ m, EvalMod S F ϖ h φ Q (σ Q) m) (n k m : ℕ) :
    ∃ y r : S, (y : B) = ltIter ϖ q n Q ∧ (r : B) = σ (ltIter ϖ q n Q) ∧
      ∃ D, Ideal.Quotient.mk (nearI S F E.mem k m) y ^ D = 0 ∧
        tev (gq E h hh k m) (Ideal.Quotient.mk _ y) D φ = Ideal.Quotient.mk _ r := by
  induction n with
  | zero =>
    refine ⟨Q, ⟨σ Q, hσS _ Q.2⟩, rfl, rfl, ?_⟩
    obtain ⟨D₀, hD₀⟩ := hnil k m
    obtain ⟨D₁, hD₁⟩ := hev m k
    refine ⟨max D₀ D₁, ?_, ?_⟩
    · exact pow_eq_zero_of_le (le_max_left _ _) hD₀
    · obtain ⟨p, hp, hpe⟩ := tev_gq E h hh k m (max D₀ D₁) φ Q
      rw [hpe, Ideal.Quotient.eq, mem_nearI]
      have := hD₁ (max D₀ D₁) (le_max_right _ _)
      rw [← hp] at this
      simpa using this
  | succ n ih =>
    obtain ⟨y, r, hy, hr, D, hD, hv⟩ := ih
    let wS : S := ⟨ϖ, E.mem⟩
    have hg : gq E h hh k m π = Ideal.Quotient.mk _ wS := by
      simp only [gq, RingHom.comp_apply]
      congr 1
      exact Subtype.ext hπ
    refine ⟨wS * y + y ^ q, wS * r + r ^ q, ?_, ?_, D, ?_, ?_⟩
    · rw [ltIter_succ, ← hy]
      simp [wS]
    · rw [ltIter_succ, map_add, map_mul, map_pow, hσϖ, ← hr]
      simp [wS]
    · rw [map_add, map_mul, map_pow]
      exact lt_pow_zero hq hD
    · have := tev_comm (gq E h hh k m) π hq φ h0 hc hD
      rw [hv, hg] at this
      rw [map_add, map_mul, map_pow, this]
      simp

theorem tev_second {A : Type} [CommRing A] (g : R →+* A) {y : A} {D : ℕ} (hy : y ^ D = 0)
    (φ : PowerSeries R) (h0 : PowerSeries.constantCoeff φ = 0) :
    ∃ W, tev g y D φ = g (PowerSeries.coeff 1 φ) * y + y ^ 2 * W := by
  obtain ⟨ρ, hρ⟩ : (PowerSeries.X : PowerSeries R) ^ 2 ∣
      φ - PowerSeries.C (PowerSeries.coeff 1 φ) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [h0]
    · simp
  have hφ : φ = PowerSeries.C (PowerSeries.coeff 1 φ) * PowerSeries.X + PowerSeries.X ^ 2 * ρ := by
    rw [← hρ]; ring
  refine ⟨tevHom g y D hy ρ, ?_⟩
  rw [← tevHom_apply g y D hy]
  conv_lhs => rw [hφ]
  rw [map_add, map_mul, map_mul, map_pow, tevHom_C, tevHom_X]

theorem est (E : PerEnv S F ϖ) {ϖ' : B} (hϖ' : ϖ * ϖ' = 1) {y : ℕ → B} (hy : ∀ n, y n ∈ S) {t : B}
    {c N₀ k : ℕ} (h0 : ∀ n ≥ N₀, Near S ϖ (F k) 0 (ϖ ^ c * (ϖ' ^ n * y n - t))) (e : ℕ) :
    ∃ u ∈ S, y (e + (c + N₀)) - ϖ ^ e * u ∈ F k := by
  set n := e + (c + N₀) with hn
  obtain ⟨s₁, hs₁, h₁⟩ := h0 n (by omega)
  obtain ⟨s₂, hs₂, h₂⟩ := h0 N₀ le_rfl
  refine ⟨ϖ ^ c * y N₀ + ϖ ^ N₀ * (s₁ - s₂),
    S.add_mem (S.mul_mem (S.pow_mem E.mem c) (hy _))
      (S.mul_mem (S.pow_mem E.mem _) (S.sub_mem hs₁ hs₂)), ?_⟩
  have hP : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ', one_pow]
  have hP₀ : ϖ ^ N₀ * ϖ' ^ N₀ = 1 := by rw [← mul_pow, hϖ', one_pow]
  have e1 : y n - ϖ ^ e * (ϖ ^ c * y N₀ + ϖ ^ N₀ * (s₁ - s₂)) =
      ϖ ^ (e + N₀) * ((ϖ ^ c * (ϖ' ^ n * y n - t) - ϖ ^ 0 * s₁) -
        (ϖ ^ c * (ϖ' ^ N₀ * y N₀ - t) - ϖ ^ 0 * s₂)) := by
    have hn' : ϖ ^ n = ϖ ^ e * ϖ ^ c * ϖ ^ N₀ := by rw [hn]; ring
    rw [hn'] at hP
    linear_combination (-(y n)) * hP + (ϖ ^ e * ϖ ^ c * y N₀) * hP₀
  rw [e1]
  exact (F k).mul_mem_left _ ((F k).sub_mem h₁ h₂)

theorem small {J : Ideal B} {P x y w s u : B} {c m n e d : ℕ} (hϖ : ϖ ∈ S)
    (hP : ϖ ^ n * P = 1) (hs : s ∈ S) (hu : u ∈ S) (hw : w ∈ S)
    (he : c + 2 * e = n + m + d)
    (hx : x - y ^ 2 * w - ϖ ^ (m + n) * s ∈ J) (hy : y - ϖ ^ e * u ∈ J) :
    Near S ϖ J m (ϖ ^ c * P * x) := by
  refine ⟨ϖ ^ c * s + ϖ ^ d * u ^ 2 * w, S.add_mem (S.mul_mem (S.pow_mem hϖ c) hs)
    (S.mul_mem (S.mul_mem (S.pow_mem hϖ d) (S.pow_mem hu 2)) hw), ?_⟩
  have hcomb : ϖ ^ c * ϖ ^ (2 * e) = ϖ ^ n * ϖ ^ m * ϖ ^ d := by
    rw [← pow_add, ← pow_add, ← pow_add, he]
  have e1 : ϖ ^ c * P * x - ϖ ^ m * (ϖ ^ c * s + ϖ ^ d * u ^ 2 * w) =
      ϖ ^ c * P * (x - y ^ 2 * w - ϖ ^ (m + n) * s) +
        ϖ ^ c * P * (y + ϖ ^ e * u) * w * (y - ϖ ^ e * u) := by
    linear_combination (ϖ ^ (c + m) * s + ϖ ^ (m + d) * u ^ 2 * w) * hP + (P * w * u ^ 2) * hcomb
  rw [e1]
  exact J.add_mem (J.mul_mem_left _ hx) (J.mul_mem_left _ hy)

end Abs

end GlobalTheory.CompanionTheory.LTPer.LogGal

namespace GlobalTheory.CompanionTheory.LTPer

open LogGal in

theorem galois_log : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {R : Type} [CommRing R], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (h : R →+* B), (∀ c, h c ∈ S) → ∀ (π : R), h π = ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ →
    ∀ (σ : B →+* B), (∀ s ∈ S, σ s ∈ S) → (∀ k, ∀ x ∈ F k, σ x ∈ F k) → σ ϖ = ϖ →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      (∀ m, EvalMod S F ϖ h φ Q (σ Q) m) →
    ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → σ t = h (PowerSeries.coeff 1 φ) * t := by
  intro B _ S F ϖ R _ E ϖ' hϖ' h hh π hπ q hq _ φ h0 hc σ hσS hσF hσϖ Q hQ hM hev t hT
  obtain ⟨M, -, hN⟩ := hM
  set a := h (PowerSeries.coeff 1 φ) with ha_def
  have ha : a ∈ S := hh _
  have hσϖ' : σ ϖ' = ϖ' := by
    have e2 : ϖ * σ ϖ' = 1 := by
      have := congrArg σ hϖ'
      rwa [map_mul, hσϖ, map_one] at this
    linear_combination (-(σ ϖ')) * hϖ' + ϖ' * e2
  have hnil := nilp_of_near E ⟨Q, hQ⟩ hN
  have hy : ∀ n, ltIter ϖ q n Q ∈ S := fun n => ltIter_mem E.mem q n hQ
  have key : ∀ k, σ t - a * t ∈ F k := by
    intro k
    obtain ⟨c, hT'⟩ := hT k
    obtain ⟨N₀, hN₀⟩ := hT' 0
    have hnear : ∀ m, Near S ϖ (F k) m (ϖ ^ c * (σ t - a * t)) := by
      intro m
      obtain ⟨N, hNm⟩ := hT' m
      obtain ⟨e, he⟩ : ∃ e, e = N + N₀ + m + 2 * (c + N₀) := ⟨_, rfl⟩
      obtain ⟨n, hn⟩ : ∃ n, n = e + (c + N₀) := ⟨_, rfl⟩
      obtain ⟨d, hd⟩ : ∃ d, c + 2 * e = n + m + d := ⟨c + 2 * e - (n + m), by omega⟩
      have hE1 := hNm n (by omega)
      have hE2 := near_map σ hσS (hσF k) hσϖ hE1
      have hE3 := near_mul ha hE1
      obtain ⟨u, hu, hu'⟩ := est E hϖ' hy hN₀ e
      rw [← hn] at hu'
      obtain ⟨yS, r, hyS, hr, D, hD, hv⟩ :=
        iter_val E h hh π hπ hq φ h0 hc σ hσS hσϖ ⟨Q, hQ⟩ hnil hev n k (m + n)
      obtain ⟨W, hW⟩ := tev_second (gq E h hh k (m + n)) hD φ h0
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective W
      rw [hv] at hW
      have hmem : r - ((⟨a, ha⟩ : S) * yS + yS ^ 2 * w) ∈ nearI S F E.mem k (m + n) := by
        rw [← Ideal.Quotient.eq, hW, map_add, map_mul, map_mul, map_pow]
        rfl
      rw [mem_nearI] at hmem
      obtain ⟨s, hs, hx⟩ := hmem
      have hP : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ', one_pow]
      have hx' : (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) - ltIter ϖ q n Q ^ 2 * (w : B)
          - ϖ ^ (m + n) * s ∈ F k := by
        have e1 : (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) - ltIter ϖ q n Q ^ 2 * (w : B)
            - ϖ ^ (m + n) * s = ((r - ((⟨a, ha⟩ : S) * yS + yS ^ 2 * w) : S) : B) - ϖ ^ (m + n) * s := by
          push_cast
          rw [hr, hyS]
          ring
        rw [e1]
        exact hx
      have hE4 := small E.mem hP hs hu w.2 hd hx' hu'
      have e2 : ϖ ^ c * (σ t - a * t) =
          a * (ϖ ^ c * (ϖ' ^ n * ltIter ϖ q n Q - t)) -
            σ (ϖ ^ c * (ϖ' ^ n * ltIter ϖ q n Q - t)) +
            ϖ ^ c * ϖ' ^ n * (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) := by
        simp only [map_mul, map_pow, map_sub, hσϖ, hσϖ']
        ring
      rw [e2]
      exact near_add (near_sub hE3 hE2) hE4
    obtain ⟨x, hx, hxF⟩ := hnear 0
    have hxk : x ∈ F k := by
      refine E.closed k x hx fun m => ?_
      obtain ⟨s, hs, hsF⟩ := hnear m
      refine ⟨s, hs, ?_⟩
      have e3 : x - ϖ ^ m * s = (ϖ ^ c * (σ t - a * t) - ϖ ^ m * s) -
          (ϖ ^ c * (σ t - a * t) - ϖ ^ 0 * x) := by ring
      rw [e3]
      exact (F k).sub_mem hsF hxF
    have hd : ϖ ^ c * (σ t - a * t) ∈ F k := by
      have e4 : ϖ ^ c * (σ t - a * t) = (ϖ ^ c * (σ t - a * t) - ϖ ^ 0 * x) + x := by ring
      rw [e4]
      exact (F k).add_mem hxF hxk
    have hP : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hϖ', one_pow]
    have e5 : σ t - a * t = ϖ' ^ c * (ϖ ^ c * (σ t - a * t)) := by
      linear_combination (-(σ t - a * t)) * hP
    rw [e5]
    exact (F k).mul_mem_left _ hd
  exact sub_eq_zero.1 (E.sep _ key)

end GlobalTheory.CompanionTheory.LTPer
