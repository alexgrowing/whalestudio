import Mathlib

open NumberField

noncomputable section

namespace PI.DIP.Loc

variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

abbrev T : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl

theorem T_le : T K p ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    (Ideal.primeCompl_le_nonZeroDivisors _)

abbrev A : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (T K p) (T_le K p)

variable {K p}

theorem mem_T {t : 𝓞 K} (ht : t ∈ T K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : 𝓞 K, (s : 𝓞 K) = u * t := by
  obtain ⟨z, hz, rfl⟩ := Submonoid.mem_map.mp ht
  have hz' : ¬ (p : ℤ) ∣ z := fun h => hz (Ideal.mem_span_singleton.mpr h)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, z = n ∨ z = -n := ⟨z.natAbs, Int.natAbs_eq z⟩
  have hcop : Nat.Coprime n p := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hz' ?_)
    have h' : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr h
    rcases hn with hn | hn <;> rw [hn]
    · exact h'
    · exact (dvd_neg).mpr h'
  refine ⟨n, hcop, ?_⟩
  rcases hn with hn | hn <;> subst hn
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

theorem surjK (a : A K p) : ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : 𝓞 K, (s : K) * (a : K) = (x : K) := by
  obtain ⟨⟨x, t⟩, h⟩ := IsLocalization.surj (T K p) a
  have hK : (a : K) * ((t : 𝓞 K) : K) = (x : K) := congrArg (fun b : A K p => (b : K)) h
  obtain ⟨s, hs, u, hu⟩ := mem_T t.2
  refine ⟨s, hs, u * x, ?_⟩
  have hu' : (s : K) = (u : K) * ((t : 𝓞 K) : K) := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hu
    simpa using this
  rw [hu', show ((u * x : 𝓞 K) : K) = (u : K) * (x : K) from rfl, ← hK]
  ring

theorem common_denom {ι : Type*} [Fintype ι] (c : ι → A K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : ι → 𝓞 K, ∀ i, (s : K) * (c i : K) = (x i : K) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (T K p) c
  choose x hx using hb
  obtain ⟨s, hs, u, hu⟩ := mem_T b.2
  refine ⟨s, hs, fun i => u * x i, fun i => ?_⟩
  have hK : ((x i : 𝓞 K) : K) = ((b : 𝓞 K) : K) * (c i : K) :=
    congrArg (fun y : A K p => (y : K)) (hx i)
  have hu' : (s : K) = (u : K) * ((b : 𝓞 K) : K) := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hu
    simpa using this
  rw [hu', show ((u * x i : 𝓞 K) : K) = (u : K) * (x i : K) from rfl, hK]
  ring

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_of_mem_span (Y : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span (A K p) (Y : Set V)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • v ∈ Y := by
  have hnat : ∀ (n : ℕ) {w : V}, w ∈ Y → (n : K) • w ∈ Y := fun n w hw => by
    rw [Nat.cast_smul_eq_nsmul]
    exact Y.nsmul_mem hw n
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : K) • (x + y) = (t : K) • ((s : K) • x) + (s : K) • ((t : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : K) (s : K)]
    rw [e]
    exact Y.add_mem (hnat t hsx) (hnat s hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, y, hy⟩ := surjK a
    refine ⟨t * s, Nat.Coprime.mul_left ht hs, ?_⟩
    have e : ((t * s : ℕ) : K) • (a • x) = y • ((s : K) • x) := by
      rw [Subalgebra.smul_def, smul_smul, ← algebraMap_smul K y, smul_smul, Nat.cast_mul,
        ← RingOfIntegers.coe_eq_algebraMap, ← hy]
      ring_nf
    rw [e]
    exact Y.smul_mem y hsx

def LocBasisProp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (p : ℕ), p.Prime →
    ∀ Y : Submodule (𝓞 K) V, Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 K, (s : K) • y = ∑ i, ((c i : 𝓞 K) : K) • b i

theorem isPID (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    IsPrincipalIdealRing (A K p) := by
  have : IsDedekindDomain (A K p) := IsLocalization.isDedekindDomain (𝓞 K) (T_le K p) (A K p)
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out)
  have hP0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K)
    (Ideal.span {(p : ℤ)}) hP0

theorem main : LocBasisProp := by
  intro K _ _ V _ _ _ _ p hp Y hY
  have : Fact p.Prime := ⟨hp⟩
  have := isPID K p
  set Y' : Submodule (A K p) V := Submodule.span (A K p) (Y : Set V) with hY'
  have : Module.Finite (A K p) Y' := by
    obtain ⟨S, hS⟩ := hY
    rw [Module.Finite.iff_fg]
    refine ⟨S, ?_⟩
    rw [hY', ← hS, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A K p) Y' := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a m h => ?_
    have hV : (a : K) • (m : V) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.mp hV with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h0)
  obtain ⟨r, B⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A K p) (M := Y')
  refine ⟨r, fun i => (B i : V), ?_, fun i => smul_mem_of_mem_span Y (B i).2, ?_⟩
  · have h1 : LinearIndependent (A K p) (fun i => (B i : V)) :=
      B.linearIndependent.map' Y'.subtype Y'.ker_subtype
    exact (LinearIndependent.iff_fractionRing (A K p) K).mp h1
  · intro y hy
    have hy' : y ∈ Y' := Submodule.subset_span hy
    obtain ⟨s, hs, x, hx⟩ := common_denom (fun i => B.repr ⟨y, hy'⟩ i)
    refine ⟨s, hs, x, ?_⟩
    have hsum : (∑ i, B.repr ⟨y, hy'⟩ i • (B i : V)) = y := by
      have := congrArg Subtype.val (B.sum_repr ⟨y, hy'⟩)
      rw [Submodule.coe_sum] at this
      exact this
    conv_lhs => rw [← hsum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.smul_def, smul_smul, hx i]

end PI.DIP.Loc
