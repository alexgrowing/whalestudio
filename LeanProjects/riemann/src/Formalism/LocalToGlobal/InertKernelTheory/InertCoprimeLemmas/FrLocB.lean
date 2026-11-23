import Formalism.LocalToGlobal.InertKernelTheory.DefsFrONB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsometryLinkageTrivialLevel
import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual

noncomputable section

namespace Formalism.L2.KerInert.FrLocB

open NumberField

section Gen

variable {K : Type*} [Field K] [NumberField K]

theorem spanPrime (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

attribute [local instance] spanPrime

abbrev Sp (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl

theorem Sp_le (p : ℕ) [hp : Fact p.Prime] : Sp K p ≤ nonZeroDivisors (𝓞 K) := by
  rintro _ ⟨x, hx, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  apply hx
  have hx0 : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (h.trans (map_zero _).symm)
  rw [hx0]
  exact Ideal.zero_mem _

theorem nat_of_Sp {p : ℕ} [hp : Fact p.Prime] {t : 𝓞 K} (ht : t ∈ Sp K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : 𝓞 K, (s : 𝓞 K) = u * t := by
  obtain ⟨x, hx, rfl⟩ := ht
  refine ⟨x.natAbs, ?_, ?_⟩
  · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hx ?_)
    exact Ideal.mem_span_singleton.mpr (Int.ofNat_dvd_left.mpr h)
  · have hc : ((x.natAbs : ℕ) : 𝓞 K) = ((x.natAbs : ℤ) : 𝓞 K) := (Int.cast_natCast _).symm
    rcases Int.natAbs_eq x with h | h
    · refine ⟨1, ?_⟩
      rw [one_mul, algebraMap_int_eq, eq_intCast, hc, ← h]
    · refine ⟨-1, ?_⟩
      rw [algebraMap_int_eq, eq_intCast, hc, neg_one_mul, ← Int.cast_neg, ← neg_eq_iff_eq_neg.mpr h]

theorem exists_loc_basis {V : Type*} [AddCommGroup V] [Module K V] (p : ℕ) [hp : Fact p.Prime]
    (A : AddSubgroup V) (hfg : A.FG) (hO : ∀ (c : 𝓞 K) (y : V), y ∈ A → ((c : K)) • y ∈ A) :
    ∃ (n : ℕ) (b : Fin n → V), LinearIndependent K b ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ A) ∧
      ∀ y ∈ A, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin n → 𝓞 K, (s : K) • y = ∑ i, ((c i : K)) • b i := by
  classical
  obtain ⟨T, hT⟩ := hfg
  have hS := Sp_le (K := K) p
  let R := Localization.subalgebra.ofField K (Sp K p) hS
  haveI : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K) hS R
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.out.ne_zero]
  haveI : IsPrincipalIdealRing R :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) (Ideal.span {(p : ℤ)}) hp0 (Sₚ := R)
  haveI : IsScalarTower R K V := IsScalarTower.of_algebraMap_smul (fun r v => rfl)
  let M : Submodule R V := Submodule.span R (T : Set V)
  haveI : Module.Finite R M := Module.Finite.span_of_finite R T.finite_toSet
  haveI : Module.IsTorsionFree R V := ⟨fun r hr x y h => by
    have hr0 : (r : K) ≠ 0 := fun h0 => hr.ne_zero (Subtype.ext h0)
    exact smul_right_injective V hr0 h⟩
  haveI : Module.IsTorsionFree R M :=
    Function.Injective.moduleIsTorsionFree M.subtype Subtype.val_injective (fun r m => rfl)
  obtain ⟨n, bas⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := M)
  have natsmul : ∀ (s : ℕ) (y : V), y ∈ A → (s : K) • y ∈ A := fun s y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact A.nsmul_mem hy s
  have key : ∀ x ∈ M, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • x ∈ A := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, Nat.coprime_one_left p, by rw [Nat.cast_one, one_smul, ← hT]; exact AddSubgroup.subset_closure hy⟩
    | zero => exact ⟨1, Nat.coprime_one_left p, by rw [smul_zero]; exact A.zero_mem⟩
    | add x y _ _ h1 h2 =>
      obtain ⟨s1, hs1, m1⟩ := h1
      obtain ⟨s2, hs2, m2⟩ := h2
      refine ⟨s1 * s2, Nat.Coprime.mul_left hs1 hs2, ?_⟩
      have e : ((s1 * s2 : ℕ) : K) • (x + y) = (s2 : K) • ((s1 : K) • x) + (s1 : K) • ((s2 : K) • y) := by
        rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (s2 : K) (s1 : K)]
      rw [e]
      exact A.add_mem (natsmul _ _ m1) (natsmul _ _ m2)
    | smul r x _ h =>
      obtain ⟨s, hs, m⟩ := h
      obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (Sp K p) r
      obtain ⟨s0, hs0, u, hu⟩ := nat_of_Sp (K := K) t.2
      refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
      have hatK : (r : K) * ((t : 𝓞 K) : K) = ((a : 𝓞 K) : K) := congrArg Subtype.val hat
      have hs0K : ((s0 : ℕ) : K) = ((u : 𝓞 K) : K) * ((t : 𝓞 K) : K) := by
        rw [← map_natCast (algebraMap (𝓞 K) K) s0, hu, map_mul]
      have e : ((s0 * s : ℕ) : K) • (r • x) = (((u * a : 𝓞 K)) : K) • ((s : K) • x) := by
        show ((s0 * s : ℕ) : K) • ((r : K) • x) = _
        rw [smul_smul, smul_smul, Nat.cast_mul, hs0K]
        congr 1
        rw [show (((u * a : 𝓞 K)) : K) = ((u : 𝓞 K) : K) * ((a : 𝓞 K) : K) from rfl, ← hatK]
        ring
      rw [e]
      exact hO _ _ m
  refine ⟨n, fun i => (bas i : V), ?_, fun i => key _ (bas i).2, ?_⟩
  · have h1 : LinearIndependent R (M.subtype ∘ bas) := bas.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    exact (LinearIndependent.iff_fractionRing (R := R) (K := K)).1 h1
  · intro y hy
    have hyM : y ∈ M := by
      rw [← hT] at hy
      exact (AddSubgroup.closure_le M.toAddSubgroup).2 (fun z hz => Submodule.subset_span hz) hy
    have hsum := congrArg Subtype.val (bas.sum_repr ⟨y, hyM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite (Sp K p) (fun i => bas.repr ⟨y, hyM⟩ i)
    choose a ha using ht
    obtain ⟨s0, hs0, u, hu⟩ := nat_of_Sp (K := K) t.2
    refine ⟨s0, hs0, fun i => u * a i, ?_⟩
    have hs0K : ((s0 : ℕ) : K) = ((u : 𝓞 K) : K) * ((t : 𝓞 K) : K) := by
      rw [← map_natCast (algebraMap (𝓞 K) K) s0, hu, map_mul]
    have haK : ∀ i, ((a i : 𝓞 K) : K) = ((t : 𝓞 K) : K) * ((bas.repr ⟨y, hyM⟩ i : R) : K) := by
      intro i
      have := congrArg Subtype.val (ha i)
      exact this
    conv_lhs => rw [← hsum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ((s0 : ℕ) : K) • (((bas.repr ⟨y, hyM⟩ i : R) : K) • (bas i : V)) = _
    rw [smul_smul, hs0K]
    congr 1
    rw [show (((u * a i : 𝓞 K)) : K) = ((u : 𝓞 K) : K) * ((a i : 𝓞 K) : K) from rfl, haK i]
    ring

theorem uniform_den {V : Type*} [AddCommGroup V] [Module K V] (p : ℕ) {n : ℕ} (b : Fin n → V) (T : Finset V)
    (h : ∀ y ∈ T, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin n → 𝓞 K, (s : K) • y = ∑ i, ((c i : K)) • b i) :
    ∃ S : ℕ, Nat.Coprime S p ∧ ∀ y ∈ AddSubgroup.closure (T : Set V),
      ∃ c : Fin n → 𝓞 K, (S : K) • y = ∑ i, ((c i : K)) • b i := by
  classical
  choose! s hs c hc using h
  refine ⟨∏ y ∈ T, s y, Nat.Coprime.prod_left fun y hy => hs y hy, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    refine ⟨fun i => ((∏ z ∈ T.erase y, s z : ℕ) : 𝓞 K) * c y i, ?_⟩
    rw [← Finset.mul_prod_erase T s hy, Nat.cast_mul, mul_comm, mul_smul, hc y hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    rw [smul_add, h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ← add_smul]
    push_cast
    rfl
  | neg x _ hx =>
    obtain ⟨c1, h1⟩ := hx
    refine ⟨-c1, ?_⟩
    rw [smul_neg, h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.neg_apply, ← neg_smul]
    push_cast
    rfl

theorem exists_loc_basis_unif {V : Type*} [AddCommGroup V] [Module K V] (p : ℕ) [hp : Fact p.Prime]
    (A : AddSubgroup V) (hfg : A.FG) (hO : ∀ (c : 𝓞 K) (y : V), y ∈ A → ((c : K)) • y ∈ A) :
    ∃ (n : ℕ) (b : Fin n → V), LinearIndependent K b ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ A) ∧
      ∃ S : ℕ, Nat.Coprime S p ∧ ∀ y ∈ A, ∃ c : Fin n → 𝓞 K, (S : K) • y = ∑ i, ((c i : K)) • b i := by
  obtain ⟨n, b, hli, hmem, hsp⟩ := exists_loc_basis p A hfg hO
  obtain ⟨T, hT⟩ := hfg
  obtain ⟨S, hS, hSp⟩ := uniform_den p b T (fun y hy => hsp y (hT ▸ AddSubgroup.subset_closure hy))
  exact ⟨n, b, hli, hmem, S, hS, fun y hy => hSp y (hT ▸ hy)⟩

end Gen

section IntAt

variable {K : Type*} [Field K] (p : ℕ)

def IntAt (x : K) : Prop := ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : K) * x)

theorem isInt_cast {R : Type*} [CommRing R] {i1 i2 : Algebra ℤ R} {x : R} (h : @IsIntegral ℤ R _ _ i1 x) :
    @IsIntegral ℤ R _ _ i2 x := by
  have e : i1 = i2 := Subsingleton.elim _ _
  subst e
  exact h

theorem isInt_nat (t : ℕ) : IsIntegral ℤ (t : K) := by
  have h := isIntegral_algebraMap (R := ℤ) (A := K) (x := (t : ℤ))
  rwa [map_natCast] at h

theorem isInt_int (t : ℤ) : IsIntegral ℤ (t : K) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := t)

theorem intAt_of_int {x : K} (h : IsIntegral ℤ x) : IntAt p x :=
  ⟨1, Nat.coprime_one_left _, by simpa using h⟩

theorem intAt_mul {x y : K} (hx : IntAt p x) (hy : IntAt p y) : IntAt p (x * y) := by
  obtain ⟨s, hs, hx'⟩ := hx
  obtain ⟨t, ht, hy'⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
  have e : ((s * t : ℕ) : K) * (x * y) = ((s : K) * x) * ((t : K) * y) := by push_cast; ring
  rw [e]
  exact isInt_cast (hx'.mul hy')

theorem intAt_add {x y : K} (hx : IntAt p x) (hy : IntAt p y) : IntAt p (x + y) := by
  obtain ⟨s, hs, hx'⟩ := hx
  obtain ⟨t, ht, hy'⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
  have e : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
    push_cast; ring
  rw [e]
  exact isInt_cast (((isInt_nat (K := K) t).mul (isInt_cast hx')).add ((isInt_nat (K := K) s).mul (isInt_cast hy')))

theorem intAt_zero : IntAt p (0 : K) := intAt_of_int p isIntegral_zero

theorem intAt_one : IntAt p (1 : K) := intAt_of_int p isIntegral_one

theorem intAt_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IntAt p (f i)) : IntAt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAt_zero (K := K) p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAt_add p (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intAt_prod {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IntAt p (f i)) : IntAt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAt_one (K := K) p
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact intAt_mul p (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intAt_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K) (h : ∀ i j, IntAt p (M i j)) :
    IntAt p M.det := by
  rw [Matrix.det_apply]
  refine intAt_sum p _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact intAt_mul p (intAt_of_int p (isInt_int _)) (intAt_prod p _ _ fun i _ => h _ _)

theorem norm_le_one_of_int {k : Type*} [NormedField k] [IsUltrametricDist k] {y : k}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨P, hPm, hP⟩ := hy
  have hsum : y ^ P.natDegree = -∑ i ∈ Finset.range P.natDegree, (P.coeff i : k) * y ^ i := by
    have h := hP
    rw [hPm.as_sum] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, algebraMap_int_eq, eq_intCast] at h
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Polynomial.C_eq_intCast, Polynomial.eval₂_C]
    simp
  have hy1 : 1 ≤ ‖y‖ := hlt.le
  rcases Nat.eq_zero_or_pos P.natDegree with hn | hn
  · rw [hn, pow_zero, Finset.range_zero, Finset.sum_empty, neg_zero] at hsum
    exact one_ne_zero hsum
  · have hle : ‖∑ i ∈ Finset.range P.natDegree, (P.coeff i : k) * y ^ i‖ ≤ ‖y‖ ^ (P.natDegree - 1) := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
      rw [norm_mul, norm_pow]
      have hc : ‖(P.coeff i : k)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one ..
      have hp : ‖y‖ ^ i ≤ ‖y‖ ^ (P.natDegree - 1) :=
        pow_le_pow_right₀ hy1 (by have := Finset.mem_range.mp hi; omega)
      calc ‖(P.coeff i : k)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (P.natDegree - 1) :=
            mul_le_mul hc hp (by positivity) zero_le_one
        _ = ‖y‖ ^ (P.natDegree - 1) := one_mul _
    rw [← norm_neg, ← hsum, norm_pow] at hle
    have hlt2 : ‖y‖ ^ (P.natDegree - 1) < ‖y‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
    linarith

theorem norm_nat_coprime [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : ((s : ℚ_[p]) : ℂ_[p]) = (s : ℂ_[p]) := map_natCast (algebraMap ℚ_[p] ℂ_[p]) s
  rw [← h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  first
  | exact h.symm
  | exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp h.symm

theorem norm_le_of_intAt [Fact p.Prime] (ψ : K →+* ℂ_[p]) {x : K} (h : IntAt p x) : ‖ψ x‖ ≤ 1 := by
  obtain ⟨s, hs, hx⟩ := h
  have h1 : ‖ψ ((s : K) * x)‖ ≤ 1 := by
    letI : Algebra ℤ ℂ_[p] := Ring.toIntAlgebra _
    exact norm_le_one_of_int (isInt_cast (hx.map ψ.toIntAlgHom))
  rwa [map_mul, map_natCast, norm_mul, norm_nat_coprime p hs, one_mul] at h1

theorem ne_zero_of_coprime [hp : Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : s ≠ 0 := by
  rintro rfl
  exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).mp h)

end IntAt

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

section Lat

variable {D : D7}

abbrev AAs (D : D7) : Submodule (𝓞 D.host.E) D.host.E := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)

abbrev IsInt (x : D.host.E) : Prop := x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)

theorem isInt_one : IsInt (D := D) 1 := Submodule.mem_one.mpr ⟨1, map_one _⟩

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) : x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N ↔ ∀ i, IsInt (D := D) (x i) := by
  unfold Formalism.MainNotions.StandardLatticesGL3.stdL
  rw [Submodule.mem_pi]
  exact ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

def intS (N N' : ℕ) : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) where
  carrier := {A | ∀ a c, IsInt (D := D) (A a c)}
  zero_mem' := fun a c => by simp
  add_mem' := fun {A B} hA hB a c => by simpa using Submodule.add_mem _ (hA a c) (hB a c)
  smul_mem' := fun r A hA a c => by simpa using Submodule.smul_mem _ r (hA a c)

theorem homL_le_intS (N N' : ℕ) : homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') ≤ intS (D := D) N N' := by
  unfold homL
  refine Submodule.span_le.mpr fun A hA => ?_
  show ∀ a c, IsInt (D := D) (A a c)
  intro a c
  have h1 : (Pi.single c (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    rw [mem_stdL]
    intro i
    by_cases h : i = c
    · subst h
      rw [Pi.single_eq_same]
      exact isInt_one
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  have h2 := (mem_stdL _).mp (hA _ h1) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem mem_one_by_one_lattice_iff (x : Matrix (Fin 1) (Fin 1) D.host.E) :
    x ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) ↔ x 0 0 ∈ AAs D := by
  constructor
  · intro hx
    unfold YYl at hx
    induction hx using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨a, ha, A, hA, rfl⟩ := hB
      have hA' := homL_le_intS (D := D) 1 1 hA 0 0
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hA'
      rw [Matrix.smul_apply, smul_eq_mul, ← hr, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r ha
    | zero => exact Submodule.zero_mem _
    | add B C _ _ hB hC =>
      rw [Matrix.add_apply]
      exact Submodule.add_mem _ hB hC
    | smul r B _ hB =>
      rw [Matrix.smul_apply]
      exact Submodule.smul_mem _ r hB
  · intro hx
    have hx' : x = x 0 0 • (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hx']
    unfold YYl
    refine Submodule.subset_span ?_
    rw [Set.mem_setOf_eq]
    refine ⟨x 0 0, hx, 1, ?_, rfl⟩
    unfold homL
    refine Submodule.subset_span ?_
    rw [Set.mem_setOf_eq]
    intro v hv
    rwa [Matrix.one_mulVec]

theorem one_mem_AA (D : D7) : (1 : D.host.E) ∈ AAs D := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h2 := D.host.𝔟_spec.2
    rw [h] at h2
    simp at h2
  have hb' : (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb
  show (1 : D.host.E) ∈ ((D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E)
  rw [FractionalIdeal.mem_coe]
  unfold Formalism.BasicNotions.Host.AA0
  rw [FractionalIdeal.mem_inv_iff hb']
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

theorem okK_smul_mem (c : 𝓞 D.host.K) {y : D.host.E} (hy : y ∈ AAs D) : ((c : D.host.K)) • y ∈ AAs D := by
  have hint : IsIntegral ℤ (((c : D.host.K) : D.host.E)) := by
    have h := (NumberField.RingOfIntegers.isIntegral_coe c).algebraMap (B := D.host.E)
    rw [IntermediateField.algebraMap_apply] at h
    exact isInt_cast h
  have he : algebraMap (𝓞 D.host.E) D.host.E (IsIntegralClosure.mk' (𝓞 D.host.E) _ hint) =
      ((c : D.host.K) : D.host.E) := IsIntegralClosure.algebraMap_mk' _ _ _
  have h := Submodule.smul_mem (AAs D) (IsIntegralClosure.mk' (𝓞 D.host.E) _ hint) hy
  rw [Algebra.smul_def, he] at h
  rwa [Algebra.smul_def, IntermediateField.algebraMap_apply]

theorem aa_fg (D : D7) : (AAs D).toAddSubgroup.FG := by
  haveI := FractionalIdeal.isNoetherian D.host.AA0
  have h1 : (AAs D).FG := (Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)
  have h2 := h1.restrictScalars (R := ℤ)
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

theorem nat_mult (z : D.host.E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : D.host.E) * z) := by
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  have h1 : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 hz
  obtain ⟨y, hy0, hy⟩ := h1.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rw [zsmul_eq_mul] at hy
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : D.host.E) = (y : D.host.E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hy
  · have : ((y.natAbs : ℕ) : D.host.E) = -(y : D.host.E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hy.neg

theorem exists_basis (D : D7) (p : ℕ) [hp : Fact p.Prime] :
    ∃ b : Fin (Fintype.card D.what₂.Tau) → D.host.E, LinearIndependent D.host.K b ∧
      ⊤ ≤ Submodule.span D.host.K (Set.range b) ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) • b i ∈ AAs D) ∧
      ∃ S : ℕ, Nat.Coprime S p ∧ ∀ y ∈ AAs D, ∃ c : Fin (Fintype.card D.what₂.Tau) → 𝓞 D.host.K,
        (S : D.host.K) • y = ∑ i, ((c i : D.host.K)) • b i := by
  obtain ⟨n, b, hli, hmem, S, hS, hsp⟩ := exists_loc_basis_unif (K := D.host.K) (V := D.host.E) p
    (AAs D).toAddSubgroup (aa_fg D) (fun c y hy => okK_smul_mem c hy)
  have hspan : ⊤ ≤ Submodule.span D.host.K (Set.range b) := by
    intro x _
    obtain ⟨k, hk, hint⟩ := nat_mult (D := D) x
    have hmx : (k : D.host.E) * x ∈ AAs D := by
      have := Submodule.smul_mem (AAs D) (⟨(k : D.host.E) * x, hint⟩ : 𝓞 D.host.E) (one_mem_AA D)
      have e : (⟨(k : D.host.E) * x, hint⟩ : 𝓞 D.host.E) • (1 : D.host.E) = (k : D.host.E) * x := by
        rw [Algebra.smul_def, mul_one]; rfl
      first | simpa [Algebra.smul_def] using this | (convert this using 1; exact e.symm)
    obtain ⟨c, hc⟩ := hsp _ hmx
    have hS0 : ((S : D.host.K) * (k : D.host.K)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast ne_zero_of_coprime p hS) (by exact_mod_cast hk.ne')
    have hx : x = ((S : D.host.K) * (k : D.host.K))⁻¹ • ∑ i, ((c i : D.host.K)) • b i := by
      rw [← hc]
      show x = ((S : D.host.K) * (k : D.host.K))⁻¹ • ((S : D.host.K) • ((k : D.host.E) * x))
      rw [show (k : D.host.E) * x = (k : D.host.K) • x from by
        rw [Algebra.smul_def]; rfl]
      rw [smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hS0, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hn : n = Fintype.card D.what₂.Tau := by
    rw [G0.card_eq D, Module.finrank_eq_card_basis (Module.Basis.mk hli hspan), Fintype.card_fin]
  subst hn
  exact ⟨b, hli, hspan, hmem, S, hS, hsp⟩

end Lat

section Form

variable (D : D7)

theorem hK_symm (x y : D.host.E) : G0.hK D x y = G0.cK D (G0.hK D y x) := (G0.herm D).symm y x

theorem hK_smul_left (k : D.host.K) (x y : D.host.E) : G0.hK D (k • x) y = k * G0.hK D x y := by
  simp only [G0.hK, smul_mul_assoc, map_smul, smul_eq_mul]

private theorem hK_smul_right' (k : D.host.K) (x y : D.host.E) :
    G0.hK D x (k • y) = G0.cK D k * G0.hK D x y := by
  have hc : ((G0.cK D k : D.host.K) : D.host.E) = D.host.conj (k : D.host.E) := rfl
  have e : x * D.host.conj (k • y) = G0.cK D k • (x * D.host.conj y) := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IntermediateField.algebraMap_apply,
      IntermediateField.algebraMap_apply, hc]
    ring
  simp only [G0.hK]
  rw [e, map_smul, smul_eq_mul]

theorem hK_sum_smul_right {ι : Type*} (s : Finset ι) (k : ι → D.host.K) (f : ι → D.host.E) (x : D.host.E) :
    G0.hK D x (∑ i ∈ s, k i • f i) = ∑ i ∈ s, G0.cK D (k i) * G0.hK D x (f i) := by
  rw [← Finset.sum_congr rfl fun i _ => hK_smul_right' D (k i) x (f i)]
  simp only [G0.hK, map_sum, Finset.mul_sum]

theorem hK_smul_right (k : D.host.K) (x y : D.host.E) : G0.hK D x (k • y) = G0.cK D k * G0.hK D x y :=
  hK_smul_right' D k x y

theorem cK_nat (s : ℕ) : G0.cK D (s : D.host.K) = s := map_natCast _ s

theorem cK_int {x : D.host.K} (h : IsIntegral ℤ x) : IsIntegral ℤ (G0.cK D x) :=
  h.map (G0.cK D).toIntAlgHom

theorem hK_of_mem {x y : D.host.E} (hx : x ∈ AAs D) (hy : y ∈ AAs D) : IsIntegral ℤ (G0.hK D x y) := by
  obtain ⟨c, hc⟩ := (SD.mm_unimod D x).1 hx y hy
  show IsIntegral ℤ (Algebra.trace D.host.K D.host.E (x * D.host.conj y))
  rw [← hc]
  exact isInt_cast c.2

end Form

def phiQ (D : D7) : D.host.E →+* Qbar :=
  D.host.φ₀.codRestrict Qbar (fun x => by
    rw [mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom)

theorem lamC_phi (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : D.host.E) :
    lamC lam (D.host.φ₀ x) = lam (phiQ D x) := by
  unfold lamC
  rw [dif_pos (show D.host.φ₀ x ∈ Qbar from (phiQ D x).2)]
  rfl

theorem local_orthonormal_basis : LocBasisMM := by
  classical
  intro D p _ hp5 hin lam
  obtain ⟨b, hli, hspan, hmem, S, hS, hsp⟩ := exists_basis D p
  let bm : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E := fun m => Matrix.of fun _ _ => b m
  let G : Matrix (Fin (Fintype.card D.what₂.Tau)) (Fin (Fintype.card D.what₂.Tau)) D.host.K := Matrix.of fun m k => G0.hK D (b m) (b k)
  have hmemE : ∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * b i ∈ AAs D := by
    intro i
    obtain ⟨s, hs, h⟩ := hmem i
    exact ⟨s, hs, by simpa [Algebra.smul_def] using h⟩

  have hLoc : LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) bm := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h0 := congrFun (congrFun hg 0) 0
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply, bm, Matrix.of_apply] at h0
      exact Fintype.linearIndependent_iff.1 hli g h0 i
    · intro i
      obtain ⟨s, hs, h⟩ := hmemE i
      refine ⟨s, hs, (mem_one_by_one_lattice_iff _).2 ?_⟩
      simpa [bm] using h
    · intro y hy
      obtain ⟨c, hc⟩ := hsp _ ((mem_one_by_one_lattice_iff y).1 hy)
      refine ⟨S, hS, c, ?_⟩
      refine Matrix.ext fun i j => ?_
      fin_cases i; fin_cases j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, bm, Matrix.of_apply]
      rw [Algebra.smul_def, map_natCast] at hc
      simp only [Algebra.smul_def] at hc
      exact hc

  have hGint : ∀ m k, IntAt p (G m k) := by
    intro m k
    obtain ⟨s, hs, h1⟩ := hmemE m
    obtain ⟨t, ht, h2⟩ := hmemE k
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have := hK_of_mem D h1 h2
    rw [show (s : D.host.E) * b m = (s : D.host.K) • b m from by rw [Algebra.smul_def, map_natCast],
      show (t : D.host.E) * b k = (t : D.host.K) • b k from by rw [Algebra.smul_def, map_natCast],
      hK_smul_left, hK_smul_right, cK_nat] at this
    have e : ((s * t : ℕ) : D.host.K) * G m k = (s : D.host.K) * ((t : D.host.K) * G0.hK D (b m) (b k)) := by
      simp only [G, Matrix.of_apply]; rw [Nat.cast_mul]; ring
    rw [e]; exact isInt_cast this

  let bK : Module.Basis (Fin (Fintype.card D.what₂.Tau)) D.host.K D.host.E := Module.Basis.mk hli hspan
  have hB := traceForm_nondegenerate D.host.K D.host.E
  let z := (Algebra.traceForm D.host.K D.host.E).dualBasis hB bK
  let w : Fin (Fintype.card D.what₂.Tau) → D.host.E := fun n => D.host.conj (z n)
  have hw : ∀ m n, G0.hK D (b m) (w n) = if m = n then 1 else 0 := by
    intro m n
    have h1 := LinearMap.BilinForm.apply_dualBasis_left hB bK n m
    rw [Algebra.traceForm_apply, Module.Basis.mk_apply] at h1
    show Algebra.trace D.host.K D.host.E (b m * D.host.conj (D.host.conj (z n))) = _
    rw [CU.conj_conj, mul_comm, h1]
  have hwS : ∀ n, (S : D.host.K) • w n ∈ AAs D := by
    intro n
    rw [SD.mm_unimod]
    intro y hy
    obtain ⟨c, hc⟩ := hsp y hy
    have e1 : G0.hK D ((S : D.host.K) • w n) y = G0.cK D (c n) := by
      rw [hK_smul_left, ← cK_nat D S]
      have e2 : G0.cK D (S : D.host.K) * G0.hK D (w n) y = G0.hK D (w n) ((S : D.host.K) • y) := by
        rw [hK_smul_right]
      rw [e2, hc, hK_sum_smul_right]
      rw [Finset.sum_eq_single n]
      · rw [hK_symm, hw, if_pos rfl, map_one, mul_one]
      · intro i _ hi
        rw [hK_symm, hw, if_neg hi, map_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ n) h
    show G0.hK D ((S : D.host.K) • w n) y ∈ _
    rw [e1]
    exact ⟨⟨G0.cK D (c n), isInt_cast (cK_int D (isInt_cast (c n).2))⟩, rfl⟩
  choose c' hc' using fun n => hsp _ (hwS n)
  have hSS : ((S : D.host.K) * S) ≠ 0 := by
    have : (S : D.host.K) ≠ 0 := by exact_mod_cast ne_zero_of_coprime p hS
    exact mul_ne_zero this this
  let H : Matrix (Fin (Fintype.card D.what₂.Tau)) (Fin (Fintype.card D.what₂.Tau)) D.host.K := Matrix.of fun n k => ((c' n k : D.host.K)) / ((S : D.host.K) * S)
  have hwH : ∀ n, w n = ∑ k, H n k • b k := by
    intro n
    have e := hc' n
    rw [smul_smul] at e
    calc w n = ((S : D.host.K) * S)⁻¹ • (((S : D.host.K) * S) • w n) := by
          rw [smul_smul, inv_mul_cancel₀ hSS, one_smul]
      _ = ∑ k, H n k • b k := by
          rw [e, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_smul]
          congr 1
          simp only [H, Matrix.of_apply]
          rw [div_eq_inv_mul]
  let Hc : Matrix (Fin (Fintype.card D.what₂.Tau)) (Fin (Fintype.card D.what₂.Tau)) D.host.K := Matrix.of fun k n => G0.cK D (H n k)
  have hGH : G * Hc = 1 := by
    refine Matrix.ext fun m n => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← hw m n, hwH n, hK_sum_smul_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [G, Hc, Matrix.of_apply]
    ring
  have hHint : ∀ k n, IntAt p (Hc k n) := by
    intro k n
    refine ⟨S * S, Nat.Coprime.mul_left hS hS, ?_⟩
    have e : ((S * S : ℕ) : D.host.K) * Hc k n = G0.cK D ((c' n k : D.host.K)) := by
      simp only [Hc, H, Matrix.of_apply]
      rw [← cK_nat D (S * S), ← map_mul]
      congr 1
      rw [Nat.cast_mul]
      have hS1 : (S : D.host.K) ≠ 0 := by exact_mod_cast ne_zero_of_coprime p hS
      field_simp
    rw [e]
    exact isInt_cast (cK_int D (isInt_cast (c' n k).2))

  have hdet : G.det * Hc.det = 1 := by rw [← Matrix.det_mul, hGH, Matrix.det_one]
  let ψ : D.host.K →+* ℂ_[p] := lam.comp ((phiQ D).comp (algebraMap D.host.K D.host.E))
  have hn1 : ‖ψ G.det‖ = 1 := by
    have h1 := norm_le_of_intAt p ψ (intAt_det p G hGint)
    have h2 := norm_le_of_intAt p ψ (intAt_det p Hc hHint)
    have h3 : ‖ψ G.det‖ * ‖ψ Hc.det‖ = 1 := by rw [← norm_mul, ← map_mul, hdet, map_one, norm_one]
    nlinarith [norm_nonneg (ψ G.det), norm_nonneg (ψ Hc.det)]
  refine ⟨bm, hLoc, ?_, ?_⟩
  · have e : (Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (bm m) (bm n) : D.host.K) : D.host.E))) =
        ψ.mapMatrix G := by
      ext m n
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, G, ψ, RingHom.comp_apply, lamC_phi]
      congr 3
      unfold hYY G0.hK
      simp [bm]
    rw [e, ← RingHom.map_det]
    exact hn1
  ·
    let e := Fintype.equivFin D.what₂.Tau
    let N : Matrix D.what₂.Tau D.what₂.Tau ℂ := Matrix.of fun τ τ' => embT D τ (b (e τ'))
    have hGN : (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).mapMatrix (G.submatrix e e) =
        N.transpose * N.map (starRingEnd ℂ) := by
      ext τ₁ τ₂
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, RingHom.comp_apply,
        Matrix.mul_apply, Matrix.transpose_apply, N, G, Matrix.of_apply]
      show D.host.φ₀ ((Algebra.trace D.host.K D.host.E (b (e τ₁) * D.host.conj (b (e τ₂))) : D.host.K) : D.host.E) = _
      rw [← FL.sum_tau_trace]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_mul, CU.emb_conj]
    have hGne : G.det ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
    have hNne : N.det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det hGN
      rw [← RingHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul] at h1
      exact hGne ((map_eq_zero_iff _ (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).injective).1 h1)
    let NQ : Matrix D.what₂.Tau D.what₂.Tau Qbar := Matrix.of fun τ τ' => IntegralOrthonormalChange.embQ D τ (b (e τ'))
    have hNQ : (algebraMap Qbar ℂ).mapMatrix NQ = N := by
      ext τ τ'; rfl
    have hNQne : NQ.det ≠ 0 := by
      intro h0
      apply hNne
      rw [← hNQ, ← RingHom.map_det, h0, map_zero]
    have e2 : (Matrix.of fun (τ τ' : D.what₂.Tau) =>
        lamC lam (embT D τ (bm (Fintype.equivFin D.what₂.Tau τ') 0 0))) = lam.mapMatrix NQ := by
      ext τ τ'
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, bm, NQ]
      exact IntegralOrthonormalChange.lamC_embT D lam τ _
    rw [e2, ← RingHom.map_det]
    exact (map_ne_zero lam).2 hNQne

end Formalism.L2.KerInert.FrLocB

namespace Formalism.L2.KerInert

theorem local_orthonormal_basis : LocBasisMM := FrLocB.local_orthonormal_basis

end Formalism.L2.KerInert
