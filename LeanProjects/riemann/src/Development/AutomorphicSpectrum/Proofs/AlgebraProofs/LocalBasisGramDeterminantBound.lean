import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SkewHermitianDiagonalizableStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsRealDifferentGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsNotMemSubConjStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocR

open NumberField

variable (E : Type) [Field E] [NumberField E]

def locRing (ℓ : Nat.Primes) : Subring E where
  carrier := {x | ∃ (n : ℕ) (a : 𝓞 E), ¬ (ℓ : ℕ) ∣ n ∧ (n : E) * x = a}
  mul_mem' := by
    rintro x y ⟨n, a, hn, ha⟩ ⟨m, b, hm, hb⟩
    refine ⟨n * m, a * b, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul ℓ.2).1 h with h | h
      exacts [hn h, hm h]
    · rw [Nat.cast_mul, show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from map_mul (algebraMap (𝓞 E) E) a b, ← ha, ← hb]
      ring
  one_mem' := ⟨1, 1, by simpa using ℓ.2.one_lt.ne', by simp⟩
  add_mem' := by
    rintro x y ⟨n, a, hn, ha⟩ ⟨m, b, hm, hb⟩
    refine ⟨n * m, (m : 𝓞 E) * a + (n : 𝓞 E) * b, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul ℓ.2).1 h with h | h
      exacts [hn h, hm h]
    · rw [Nat.cast_mul, show (((m : 𝓞 E) * a + (n : 𝓞 E) * b : 𝓞 E) : E) = (m : E) * (a : E) + (n : E) * (b : E) by
        simp [map_add, map_mul (algebraMap (𝓞 E) E)], ← ha, ← hb]
      ring
  zero_mem' := ⟨1, 0, by simpa using ℓ.2.one_lt.ne', by simp⟩
  neg_mem' := by
    rintro x ⟨n, a, hn, ha⟩
    refine ⟨n, -a, hn, ?_⟩
    rw [show ((-a : 𝓞 E) : E) = -(a : E) from map_neg (algebraMap (𝓞 E) E) a, ← ha]
    ring

variable {E}

theorem coe_mem_locRing (ℓ : Nat.Primes) (a : 𝓞 E) : (a : E) ∈ locRing E ℓ :=
  ⟨1, a, by simpa using ℓ.2.one_lt.ne', by simp⟩

theorem inv_natCast_mem_locRing {ℓ : Nat.Primes} {n : ℕ} (hn : ¬ (ℓ : ℕ) ∣ n) :
    ((n : E))⁻¹ ∈ locRing E ℓ := by
  have h0 : (n : E) ≠ 0 := by
    rintro h
    exact hn (by simp [Nat.cast_eq_zero.1 h])
  exact ⟨n, 1, hn, by simp [h0]⟩

variable (E)

def conjLoc [IsCMField E] (ℓ : Nat.Primes) (x : locRing E ℓ) : locRing E ℓ :=
  ⟨IsCMField.complexConj E (x : E), by
    obtain ⟨n, a, hn, ha⟩ := x.2
    refine ⟨n, ⟨IsCMField.complexConj E (a : E), ?_⟩, hn, ?_⟩
    · exact (a.2).map (IsCMField.complexConj E)
    · rw [show ((n : E)) = IsCMField.complexConj E (n : E) from (map_natCast _ n).symm, ← map_mul, ha]
      rfl⟩

instance instStarLocRing [IsCMField E] (ℓ : Nat.Primes) : StarRing (locRing E ℓ) where
  star := conjLoc E ℓ
  star_involutive x := Subtype.ext (IsCMField.complexConj_apply_apply E (x : E))
  star_mul x y := Subtype.ext (by
    change IsCMField.complexConj E ((x : E) * (y : E)) =
      IsCMField.complexConj E (y : E) * IsCMField.complexConj E (x : E)
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add (IsCMField.complexConj E) (x : E) (y : E))

variable {E}

@[simp] theorem coe_star_locRing [IsCMField E] {ℓ : Nat.Primes} (x : locRing E ℓ) :
    ((star x : locRing E ℓ) : E) = IsCMField.complexConj E (x : E) := rfl

def ofInt (ℓ : Nat.Primes) : 𝓞 E →+* locRing E ℓ :=
  (algebraMap (𝓞 E) E).codRestrict (locRing E ℓ) (coe_mem_locRing ℓ)

@[simp] theorem coe_ofInt (ℓ : Nat.Primes) (a : 𝓞 E) : ((ofInt ℓ a : locRing E ℓ) : E) = (a : E) := rfl

theorem isUnit_natCast_loc {ℓ : Nat.Primes} {n : ℕ} (hn : ¬ (ℓ : ℕ) ∣ n) :
    IsUnit ((n : locRing E ℓ)) := by
  have h0 : (n : E) ≠ 0 := fun h => hn (by simp [Nat.cast_eq_zero.1 h])
  refine IsUnit.of_mul_eq_one (⟨(n : E)⁻¹, inv_natCast_mem_locRing hn⟩ : locRing E ℓ) (Subtype.ext ?_)
  simp [h0]

theorem exists_natCast_mul_eq {ℓ : Nat.Primes} (x : locRing E ℓ) :
    ∃ (n : ℕ) (a : 𝓞 E), ¬ (ℓ : ℕ) ∣ n ∧ (n : locRing E ℓ) * x = ofInt ℓ a := by
  obtain ⟨n, a, hn, ha⟩ := x.2
  exact ⟨n, a, hn, Subtype.ext (by simpa using ha)⟩

theorem comap_injective {ℓ : Nat.Primes} {m m' : Ideal (locRing E ℓ)} (hm' : m'.IsPrime) (hm : m.IsPrime)
    (h : m.comap (ofInt ℓ) = m'.comap (ofInt ℓ)) : m ≤ m' := by
  intro x hx
  obtain ⟨n, a, hn, e⟩ := exists_natCast_mul_eq x
  have h1 : a ∈ m.comap (ofInt ℓ) := by
    rw [Ideal.mem_comap, ← e]
    exact m.mul_mem_left _ hx
  rw [h, Ideal.mem_comap, ← e] at h1
  exact (hm'.mem_or_mem h1).resolve_left fun h2 => hm'.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (isUnit_natCast_loc hn))

theorem natCast_mem_comap {ℓ : Nat.Primes} {m : Ideal (locRing E ℓ)} (hm : m.IsPrime)
    (h0 : m.comap (ofInt ℓ) ≠ ⊥) : ((ℓ : ℕ) : 𝓞 E) ∈ m.comap (ofInt ℓ) := by
  haveI : (m.comap (ofInt ℓ)).IsPrime := Ideal.comap_isPrime _ _
  set P := m.comap (ofInt ℓ) with hP
  have hN : Ideal.absNorm P ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨k, n, hn, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN (ℓ : ℕ) ℓ.2.one_lt.ne'
  have h1 : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  rw [e, Nat.cast_mul, Nat.cast_pow] at h1
  rcases (inferInstance : P.IsPrime).mem_or_mem h1 with h2 | h2
  · exact (inferInstance : P.IsPrime).mem_of_pow_mem _ h2
  · exfalso
    rw [hP, Ideal.mem_comap, map_natCast] at h2
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (isUnit_natCast_loc hn))

theorem finite_maxSpec (ℓ : Nat.Primes) : Finite (MaximalSpectrum (locRing E ℓ)) := by
  classical
  have hℓ : Ideal.span {((ℓ : ℕ) : 𝓞 E)} ≠ 0 := by
    simpa using ℓ.2.ne_zero
  haveI : Fintype {P : Ideal (𝓞 E) // P ∣ Ideal.span {((ℓ : ℕ) : 𝓞 E)}} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ hℓ
  let f : MaximalSpectrum (locRing E ℓ) → Option {P : Ideal (𝓞 E) // P ∣ Ideal.span {((ℓ : ℕ) : 𝓞 E)}} :=
    fun m => if h : m.asIdeal.comap (ofInt ℓ) = ⊥ then none else
      some ⟨m.asIdeal.comap (ofInt ℓ), Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2
        (natCast_mem_comap m.isMaximal.isPrime h))⟩
  refine Finite.of_injective f fun m m' e => ?_
  have hc : m.asIdeal.comap (ofInt ℓ) = m'.asIdeal.comap (ofInt ℓ) := by
    by_cases h : m.asIdeal.comap (ofInt ℓ) = ⊥ <;> by_cases h' : m'.asIdeal.comap (ofInt ℓ) = ⊥
    · rw [h, h']
    · simp [f, h, h'] at e
    · simp [f, h, h'] at e
    · simpa [f, h, h'] using e
  exact MaximalSpectrum.ext (m.isMaximal.eq_of_le m'.isMaximal.ne_top
    (comap_injective m'.isMaximal.isPrime m.isMaximal.isPrime hc))

section Form

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable [IsCMField E]

theorem exists_sub_star_notMem (H : Host E) (ℓ : Nat.Primes) (m : Ideal (locRing E ℓ)) (hm : m.IsMaximal) :
    ∃ a : locRing E ℓ, a - star a ∉ m := by
  haveI : (m.comap (ofInt ℓ)).IsPrime := Ideal.comap_isPrime _ _
  have key : ∃ a : 𝓞 E, a - H.bar a ∉ m.comap (ofInt ℓ) := by
    by_cases h0 : m.comap (ofInt ℓ) = ⊥
    · obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
      obtain ⟨a, ha⟩ := GlobalTheory.T.exists_not_mem_sub_conj E H.bar H.bar_eq H.unram M hM
      refine ⟨a, ?_⟩
      rw [h0, Ideal.mem_bot]
      intro h
      exact ha (h ▸ M.zero_mem)
    · exact GlobalTheory.T.exists_not_mem_sub_conj E H.bar H.bar_eq H.unram _ (Ideal.IsPrime.isMaximal inferInstance h0)
  obtain ⟨a, ha⟩ := key
  refine ⟨ofInt ℓ a, fun h => ha ?_⟩
  rw [Ideal.mem_comap, map_sub]
  convert h using 2
  exact Subtype.ext (H.bar_eq a)

variable {H : Host E}

theorem sesq_zero_left (D : Datum H) (y : D.La) : sesq D 0 y = 0 := by
  have := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1 0 0 y
  simpa using this

theorem sesq_zero_right (D : Datum H) (y : D.La) : sesq D y 0 = 0 := by
  have := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1 0 y 0
  simpa using this

theorem sesq_sum_left (D : Datum H) {ι : Type} (s : Finset ι) (a : ι → 𝓞 E) (x : ι → D.La) (y : D.La) :
    sesq D (∑ i ∈ s, a i • x i) y = ∑ i ∈ s, (a i : E) * sesq D (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_left]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1, ih,
      (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1]

theorem sesq_sum_right (D : Datum H) {ι : Type} (s : Finset ι) (a : ι → 𝓞 E) (x : ι → D.La) (y : D.La) :
    sesq D y (∑ i ∈ s, a i • x i) = ∑ i ∈ s, IsCMField.complexConj E (a i : E) * sesq D y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1, ih,
      (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1]

theorem eq_zero_of_sesq_eq_zero (D : Datum H) (y : D.La) (h : ∀ z, sesq D y z = 0) : y = 0 := by
  apply D.unimod.1
  rw [map_zero]
  ext z
  have := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).1 1 y z
  rw [one_smul, h z] at this
  simpa using this.symm

theorem gram_det_ne_zero (D : Datum H) {I : Type} [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (hx : IsLocBasis (𝓞 E) ℓ x) : (gramE D x).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v
  choose c hc using hb
  have hb0 : ((b : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero b.2
    exact_mod_cast this
  have hcv : ∀ i, (c i : E) = (b : 𝓞 E) * v i := fun i => by
    have := hc i
    rw [Algebra.smul_def] at this
    exact this
  set y : D.La := ∑ i, c i • x i with hy
  have h1 : ∀ n, sesq D y (x n) = 0 := by
    intro n
    rw [hy, sesq_sum_left]
    have := congrFun hv0 n
    simp only [Matrix.vecMul, dotProduct, gramE, Matrix.of_apply, Pi.zero_apply] at this
    simp only [hcv, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  obtain ⟨hli, N, hN, hspan⟩ := hx
  have hN0 : (N : E) ≠ 0 := fun h => hN (by simp [Nat.cast_eq_zero.1 h])
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), sesq D y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨n, rfl⟩ := hw; exact h1 n
    | zero => exact sesq_zero_right D y
    | add u w _ _ hu hw => rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1, hu, hw, add_zero]
    | smul a w _ hw => rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, hw, mul_zero]
  have h3 : y = 0 := by
    refine eq_zero_of_sesq_eq_zero D y fun z => ?_
    have := h2 _ (hspan z)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1] at this
    simpa [hN0] using this
  have h4 := Fintype.linearIndependent_iff.1 hli c h3
  apply hv
  funext i
  have := hcv i
  rw [h4 i] at this
  simpa [hb0] using this.symm

end Form

section Norm

theorem norm_le_one {ℓ : Nat.Primes} (x : locRing E ℓ) (j : E →+* ℂ_[ℓ]) : ‖j (x : E)‖ ≤ 1 :=
  (GlobalTheory.T.padic_integral_iff_denominator E ℓ (x : E)).2 x.2 j

theorem norm_eq_one_of_isUnit {ℓ : Nat.Primes} {u : locRing E ℓ} (hu : IsUnit u) (j : E →+* ℂ_[ℓ]) :
    ‖j (u : E)‖ = 1 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : ‖j (u : E)‖ * ‖j (v : E)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Subring.coe_mul, hv]
    simp
  have h2 := norm_le_one u j
  have h3 := norm_le_one v j
  nlinarith [norm_nonneg (j (u : E)), norm_nonneg (j (v : E))]

theorem isUnit_of_norm_eq_one {ℓ : Nat.Primes} (u : locRing E ℓ) (h0 : (u : E) ≠ 0)
    (h : ∀ j : E →+* ℂ_[ℓ], ‖j (u : E)‖ = 1) : IsUnit u := by
  have h1 : (u : E)⁻¹ ∈ locRing E ℓ := (GlobalTheory.T.padic_integral_iff_denominator E ℓ _).1 fun j => by
    rw [map_inv₀, norm_inv, h j, inv_one]
  exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing E ℓ) (Subtype.ext (by simp [h0]))

theorem exists_common_denom {ℓ : Nat.Primes} {ι : Type} [Fintype ι] (f : ι → locRing E ℓ) :
    ∃ (N : ℕ) (a : ι → 𝓞 E), ¬ (ℓ : ℕ) ∣ N ∧ ∀ i, (N : E) * f i = a i := by
  classical
  choose n a hn ha using fun i => (f i).2
  refine ⟨∏ i, n i, fun i => ((∏ k ∈ Finset.univ.erase i, n k : ℕ) : 𝓞 E) * a i, ?_, fun i => ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Nat.Prime.prime ℓ.2) _).1 h
    exact hn i hi
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), show (((∏ k ∈ Finset.univ.erase i, n k : ℕ) : 𝓞 E) * a i : 𝓞 E).val = ((∏ k ∈ Finset.univ.erase i, n k : ℕ) : E) * (a i : E) by
      simp [RingOfIntegers.coe_eq_algebraMap] , ← ha i]
    push_cast
    ring

end Norm

section Comb

theorem isLocBasis_comb {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] {ι : Type} [Fintype ι]
    [DecidableEq ι] {x : ι → M} {ℓ : ℕ} (hℓ : ℓ.Prime) (A B : Matrix ι ι O) (N : ℕ) (hN : ¬ ℓ ∣ N) (hN0 : (N : O) ≠ 0)
    (hBA : B * A = (N : O) • (1 : Matrix ι ι O)) (hx : IsLocBasis O ℓ x) :
    IsLocBasis O ℓ (fun a => ∑ k, A a k • x k) := by
  obtain ⟨hli, n, hn, hspan⟩ := hx
  have hdet : A.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hBA
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ hN0 this.symm
  refine ⟨?_, n * N, fun h => ?_, fun y => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : ∑ k, (∑ a, c a * A a k) • x k = 0 := by
      rw [← hc]
      simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    have h2 := Fintype.linearIndependent_iff.1 hli _ h1
    have h3 : Matrix.vecMul c A = 0 := by
      funext k
      simpa [Matrix.vecMul, dotProduct] using h2 k
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet h3
    intro i
    exact congrFun this i
  · rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    exacts [hn h, hN h]
  · have h1 : ∀ k, N • x k ∈ Submodule.span O (Set.range fun a => ∑ k, A a k • x k) := by
      intro k
      have h2 : N • x k = ∑ a, B k a • ∑ l, A a l • x l := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul]
        have h3 : ∀ l, ∑ a, B k a * A a l = (B * A) k l := fun l => (Matrix.mul_apply).symm
        simp only [h3, hBA, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        simp [ite_smul, ← Nat.cast_smul_eq_nsmul O]
      rw [h2]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    have h4 : ∀ w ∈ Submodule.span O (Set.range x), N • w ∈ Submodule.span O (Set.range fun a => ∑ k, A a k • x k) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw => obtain ⟨k, rfl⟩ := hw; exact h1 k
      | zero => simp
      | add u w _ _ hu hw => rw [smul_add]; exact Submodule.add_mem _ hu hw
      | smul a w _ hw => rw [smul_comm]; exact Submodule.smul_mem _ a hw
    rw [mul_comm, mul_smul]
    exact h4 _ (hspan y)

end Comb

section Main

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix

variable [IsCMField E]

theorem exists_diag_basis (H : Host E) (D : Datum H) (n : ℕ) (hn : n = D.p + D.q) (ℓ : Nat.Primes) :
    ∃ (x : Fin n → D.La) (δ : 𝓞 E), IsLocBasis (𝓞 E) ℓ x ∧ (δ : E) ≠ 0 ∧
      (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (δ : E)‖ =
        logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧
      (∀ a b, a ≠ b → sesq D (x a) (x b) = 0) ∧
      ∀ a, ∃ u : locRing E ℓ, IsUnit u ∧ (δ : E) * sesq D (x a) (x a) = u := by
  haveI := finite_maxSpec (E := E) ℓ
  haveI := D.fin
  haveI := D.proj
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_local_basis' E D.La (Fin n) (ℓ : ℕ) ℓ.2 (by simp [D.rank, hn])
  obtain ⟨δ, hδ, hδ0, hδc, hδj⟩ := GlobalTheory.T.exists_real_different_generator E H.unram ℓ
  have hδE : (δ : E) ≠ 0 := by exact_mod_cast hδ0
  have hint := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.2 δ hδ
  have hmem : ∀ a b, (δ : E) * sesq D (x a) (x b) ∈ locRing E ℓ := fun a b => by
    obtain ⟨c, hc⟩ := hint (x a) (x b)
    rw [hc]
    exact coe_mem_locRing ℓ c
  let G : Matrix (Fin n) (Fin n) (locRing E ℓ) := Matrix.of fun a b => ⟨_, hmem a b⟩
  have hGc : ∀ a b, ((G a b : locRing E ℓ) : E) = (δ : E) * sesq D (x a) (x b) := fun _ _ => rfl
  have hG : Gᴴ = -G := by
    ext a b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply, coe_star_locRing, hGc, Subring.coe_neg, hGc, map_mul, hδc,
      (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x b) (x a)]
    ring
  have hGdet : ((G.det : locRing E ℓ) : E) = (δ : E) ^ n * (gramE D x).det := by
    have h1 : (locRing E ℓ).subtype.mapMatrix G = (δ : E) • gramE D x := by
      ext a b
      rfl
    have h2 := RingHom.map_det (locRing E ℓ).subtype G
    rw [h1, Matrix.det_smul, Fintype.card_fin] at h2
    exact h2
  have hd0 := gram_det_ne_zero D x ℓ ℓ.2 hx
  have hGu : IsUnit G.det := by
    refine isUnit_of_norm_eq_one _ (by rw [hGdet]; exact mul_ne_zero (pow_ne_zero _ hδE) hd0) fun j => ?_
    have h1 := GlobalTheory.T.gram_determinant_log_different E H D (Fin n) x ℓ hx j
    have h2 := hδj j
    have h3 : 0 < ‖j (δ : E)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hδE)
    have h4 : 0 < ‖j (gramE D x).det‖ := norm_pos_iff.2 ((map_ne_zero j).2 hd0)
    rw [hGdet, map_mul, map_pow, norm_mul, norm_pow]
    refine Real.eq_one_of_pos_of_log_eq_zero (by positivity) ?_
    rw [Real.log_mul (by positivity) h4.ne', Real.log_pow, h1, h2, Fintype.card_fin]
    ring
  obtain ⟨T, hTu, hTd⟩ := GlobalTheory.T.skew_hermitian_diagonalizable _ n G hG hGu (exists_sub_star_notMem H ℓ)
  obtain ⟨N, A, hN, hA⟩ := exists_common_denom (ι := Fin n × Fin n) (fun q => T q.1 q.2)
  obtain ⟨N', B, hN', hB⟩ := exists_common_denom (ι := Fin n × Fin n) (fun q => T⁻¹ q.1 q.2)
  have hN0 : (N : E) ≠ 0 := fun h => hN (by simp [Nat.cast_eq_zero.1 h])
  have hN'0 : (N' : E) ≠ 0 := fun h => hN' (by simp [Nat.cast_eq_zero.1 h])
  let Am : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun a b => A (a, b)
  let Bm : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun a b => B (a, b)
  have hinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hTu
  have hBA : Bm * Am = (((N' * N : ℕ)) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
    ext a b
    have h1 : (((T⁻¹ * T) a b : locRing E ℓ) : E) = ∑ k, ((T⁻¹ a k : locRing E ℓ) : E) * (T k b : E) := by
      rw [Matrix.mul_apply]
      simp
    rw [hinv] at h1
    have h2 : ((Bm * Am) a b : E) = ∑ k, (B (a, k) : E) * (A (k, b) : E) := by
      rw [Matrix.mul_apply]
      simp [Bm, Am, RingOfIntegers.coe_eq_algebraMap]
    rw [h2]
    simp only [← hA, ← hB]
    have h3 : ∑ k, ((N' : E) * ((T⁻¹ a k : locRing E ℓ) : E)) * ((N : E) * (T k b : E)) =
        (N' : E) * N * ∑ k, ((T⁻¹ a k : locRing E ℓ) : E) * (T k b : E) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h3, ← h1]
    by_cases hab : a = b
    · subst hab
      simp [RingOfIntegers.coe_eq_algebraMap]
    · simp [hab, RingOfIntegers.coe_eq_algebraMap]
  have hNN : ¬ (ℓ : ℕ) ∣ N' * N := fun h => by
    rcases (Nat.Prime.dvd_mul ℓ.2).1 h with h | h
    exacts [hN' h, hN h]
  have hNN0 : (((N' * N : ℕ)) : 𝓞 E) ≠ 0 := by
    intro h
    have : (((N' * N : ℕ)) : E) = 0 := by
      simpa [RingOfIntegers.coe_eq_algebraMap] using congrArg (algebraMap (𝓞 E) E) h
    rw [Nat.cast_mul] at this
    exact mul_ne_zero hN'0 hN0 this
  have hx' := isLocBasis_comb ℓ.2 Am Bm (N' * N) hNN hNN0 hBA hx
  set x' : Fin n → D.La := fun a => ∑ k, Am a k • x k with hx'def
  set W := T * G * Tᴴ with hW
  have hconjN : ∀ a b, IsCMField.complexConj E ((Am a b : 𝓞 E) : E) =
      (N : E) * IsCMField.complexConj E ((T a b : locRing E ℓ) : E) := fun a b => by
    have : ((Am a b : 𝓞 E) : E) = (N : E) * (T a b : E) := (hA (a, b)).symm
    rw [this, map_mul, map_natCast]
  have hWc : ∀ a b, (W a b : E) = ∑ l, (∑ k, (T a k : E) * ((δ : E) * sesq D (x k) (x l))) *
      IsCMField.complexConj E ((T b l : locRing E ℓ) : E) := by
    intro a b
    rw [hW, Matrix.mul_apply]
    simp [Matrix.mul_apply, hGc]
  have key : ∀ a b, (δ : E) * sesq D (x' a) (x' b) = (N : E) ^ 2 * (W a b : E) := by
    intro a b
    rw [hWc, hx'def]
    simp only []
    rw [sesq_sum_left]
    simp only [sesq_sum_right, hconjN]
    have hAa : ∀ k, ((Am a k : 𝓞 E) : E) = (N : E) * (T a k : E) := fun k => (hA (a, k)).symm
    simp only [hAa, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdetW : IsUnit W.det := by
    rw [hW, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (hTu.mul hGu).mul hTu.star
  have hWu : ∀ a, IsUnit (W a a) := by
    intro a
    have h1 : W.det = ∏ i, W i i := by
      conv_lhs => rw [← hTd.diagonal_diag]
      rw [Matrix.det_diagonal]
      rfl
    rw [h1] at hdetW
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => W i i) (Finset.mem_univ a)) hdetW
  refine ⟨x', δ, hx', hδE, hδj, fun a b hab => ?_, fun a => ⟨(N : locRing E ℓ) ^ 2 * W a a,
    ((isUnit_natCast_loc hN).pow 2).mul (hWu a), ?_⟩⟩
  · have h1 := key a b
    rw [show (W a b) = 0 from hTd hab] at h1
    simpa [hδE] using h1
  · rw [key a a]
    simp

end Main

section Target

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem exists_locBasis_first_unimodular :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes),
      p + q = D.p + D.q → ∃ x : Fin p ⊕ Fin q → D.La, IsLocBasis (𝓞 E) ℓ x ∧ (gramE D (x ∘ Sum.inl)).det ≠ 0 ∧
        ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inl)).det‖ =
          -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ H D p q ℓ hpq
  obtain ⟨x, δ, hx, hδ0, hδj, hoff, hdiag⟩ := exists_diag_basis H D (p + q) hpq ℓ
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let s : Fin p → E := fun a => sesq D (x (e (.inl a))) (x (e (.inl a)))
  have hg : gramE D ((x ∘ e) ∘ Sum.inl) = Matrix.diagonal s := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [gramE, s]
    · have : e (.inl a) ≠ e (.inl b) := fun h => hab (Sum.inl_injective (e.injective h))
      simp [gramE, hab, hoff _ _ this]
  have hs0 : ∀ a, s a ≠ 0 := by
    intro a
    obtain ⟨u, hu, e1⟩ := hdiag (e (.inl a))
    intro h
    have h1 : (u : E) = 0 := by rw [← e1]; simp [s] at h; simp [h]
    exact hu.ne_zero (Subtype.ext h1)
  have hsj : ∀ (j : E →+* ℂ_[ℓ]) a, Real.log ‖j (s a)‖ = -logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
    intro j a
    obtain ⟨u, hu, e1⟩ := hdiag (e (.inl a))
    have h1 := norm_eq_one_of_isUnit hu j
    rw [← e1, map_mul, norm_mul] at h1
    have h2 : 0 < ‖j (δ : E)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hδ0)
    have h3 : 0 < ‖j (s a)‖ := norm_pos_iff.2 ((map_ne_zero j).2 (hs0 a))
    have h4 := congrArg Real.log h1
    rw [Real.log_mul h2.ne' h3.ne', Real.log_one, hδj j] at h4
    linarith
  refine ⟨x ∘ e, ⟨hx.1.comp e e.injective, ?_⟩, ?_, fun j => ?_⟩
  · obtain ⟨n, hn, hsp⟩ := hx.2
    exact ⟨n, hn, by simpa [Set.range_comp, e.surjective.range_eq] using hsp⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hs0 a
  · rw [hg, Matrix.det_diagonal, map_prod, norm_prod,
      Real.log_prod (fun a _ => (norm_pos_iff.2 ((map_ne_zero j).2 (hs0 a))).ne')]
    simp only [hsj j]
    simp

end Target

end GlobalTheory.CompanionTheory.Ar.Fl.LocR
