import Mathlib
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.LubinTateTorsion
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel

section Integers

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem card_quotient_span_eq_one_of_isUnit {a : 𝒪[K]} (ha : IsUnit a) :
    Nat.card (𝒪[K] ⧸ Ideal.span {a}) = 1 := by
  rw [Ideal.span_singleton_eq_top.2 ha]
  have : Subsingleton (𝒪[K] ⧸ (⊤ : Ideal 𝒪[K])) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_unique

theorem card_quotient_span_mul {a b : 𝒪[K]} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {a * b}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {a}) * Nat.card (𝒪[K] ⧸ Ideal.span {b}) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hπ
  have key : ∀ (v : 𝒪[K]ˣ) (n : ℕ), Ideal.span {(v : 𝒪[K]) * π ^ n} = Ideal.span {π ^ n} :=
    fun v n => Ideal.span_singleton_mul_left_unit v.isUnit _
  have hab : (u : 𝒪[K]) * π ^ i * ((w : 𝒪[K]) * π ^ j) =
      ((u * w : 𝒪[K]ˣ) : 𝒪[K]) * π ^ (i + j) := by
    push_cast
    ring
  rw [hab, key, key, key, FormalGroup.card_quotient_span_pow hπ, FormalGroup.card_quotient_span_pow hπ,
    FormalGroup.card_quotient_span_pow hπ, pow_add]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem natCast_integer_ne_zero {m : ℕ} (hm : (m : K) ≠ 0) : (m : 𝒪[K]) ≠ 0 := by
  intro h
  apply hm
  have := congrArg (fun x : 𝒪[K] => (x : K)) h
  simpa using this

theorem card_quotient_span_natCast_mul {m n : ℕ} (hm : (m : K) ≠ 0) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {((m * n : ℕ) : 𝒪[K])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) * Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) := by
  rw [Nat.cast_mul]
  exact card_quotient_span_mul (natCast_integer_ne_zero hm) (natCast_integer_ne_zero hn)

theorem card_quotient_span_natCast_pow {m : ℕ} (hm : (m : K) ≠ 0) (d : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {((m ^ d : ℕ) : 𝒪[K])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) ^ d := by
  induction d with
  | zero =>
    rw [pow_zero, pow_zero, Nat.cast_one]
    exact card_quotient_span_eq_one_of_isUnit isUnit_one
  | succ d ih =>
    have hmd : ((m ^ d : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ hm
    rw [pow_succ, card_quotient_span_natCast_mul hmd hm, ih, pow_succ]

theorem card_quotient_span_natCast_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) = 1 := by
  apply card_quotient_span_eq_one_of_isUnit
  by_contra h
  apply hm
  rw [← map_natCast (IsLocalRing.residue 𝒪[K]), IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 h

end Integers

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L]

theorem card_quotient_span_natCast_finiteExtension (m : ℕ) :
    Nat.card (𝒪[L] ⧸ Ideal.span {(m : 𝒪[L])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) ^ Module.finrank K L := by
  classical
  let ι := Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]
  let b : Module.Basis ι 𝒪[K] 𝒪[L] := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  let I : Ideal 𝒪[K] := Ideal.span {(m : 𝒪[K])}
  let ψ : 𝒪[L] →ₗ[𝒪[K]] (ι → 𝒪[K] ⧸ I) :=
    LinearMap.pi fun i => I.mkQ ∘ₗ (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap)
  have hψ : ∀ x i, ψ x i = Submodule.Quotient.mk (b.equivFun x i) := fun _ _ => rfl
  have hsmul : ∀ y : 𝒪[L], (m : 𝒪[K]) • y = (m : 𝒪[L]) * y := fun y => by
    rw [Algebra.smul_def, map_natCast]
  have hsurj : Function.Surjective ψ := by
    intro v
    refine ⟨b.equivFun.symm fun i => Quotient.out (v i), ?_⟩
    funext i
    rw [hψ, LinearEquiv.apply_symm_apply]
    exact Quotient.out_eq (v i)
  have hker : LinearMap.ker ψ = (Ideal.span {(m : 𝒪[L])}).restrictScalars 𝒪[K] := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have hc : ∀ i, ∃ c : 𝒪[K], c * (m : 𝒪[K]) = b.equivFun x i := fun i => by
        have := congrFun hx i
        rw [hψ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose c hc using hc
      refine ⟨b.equivFun.symm c, ?_⟩
      rw [mul_comm, ← hsmul]
      apply b.equivFun.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, ← hc i, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [hψ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, mul_comm, ← hsmul, map_smul,
        Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e1 : (𝒪[L] ⧸ (Ideal.span {(m : 𝒪[L])}).restrictScalars 𝒪[K]) ≃ₗ[𝒪[K]] (ι → 𝒪[K] ⧸ I) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  have e2 := Submodule.Quotient.restrictScalarsEquiv 𝒪[K] (Ideal.span {(m : 𝒪[L])})
  rw [← Nat.card_congr e2.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_fun,
    ← Module.finrank_eq_nat_card_basis b, finrank_integer]

end Extension

section Groups

theorem exists_card_eq_prime_pow_of_nsmul {A : Type*} [AddCommGroup A] [Finite A] {l : ℕ}
    [Fact l.Prime] (h : ∀ a : A, l • a = 0) : ∃ d, Nat.card A = l ^ d := by
  have hP : IsPGroup l (Multiplicative A) := fun x => ⟨1, by
    rw [pow_one]
    exact congrArg Multiplicative.ofAdd (h (Multiplicative.toAdd x))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  exact ⟨n, hn⟩

theorem exists_ne_zero_forall_mem_eq {k G : Type*} [CommRing k] [Group G] {l : ℕ} [Fact l.Prime]
    (M : Rep k G) [Finite M] [Nontrivial M] (hl : ∀ m : M, l • m = 0) (W T : Subgroup G)
    (hT : ∀ g ∈ T, ∀ m : M, M.ρ g m = m) (hW : ∀ g ∈ W, ∃ n : ℕ, g ^ l ^ n ∈ T) :
    ∃ m : M, m ≠ 0 ∧ ∀ g ∈ W, M.ρ g m = m := by
  let H := W.map (Representation.asGroupHom M.ρ)
  have hH : IsPGroup l H := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨n, hn⟩ := hW g hg
    refine ⟨n, Subtype.ext (Units.ext (LinearMap.ext fun a => ?_))⟩
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, Units.val_one, Module.End.one_apply]
    rw [← map_pow, Representation.asGroupHom_apply, hT _ hn]
  obtain ⟨d, hd⟩ := exists_card_eq_prime_pow_of_nsmul hl
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := (Finite.one_lt_card_iff_nontrivial (α := M)).2 inferInstance
    rw [hd, pow_zero] at h1
    exact lt_irrefl _ h1
  have hcard : l ∣ Nat.card M := hd ▸ dvd_pow_self l hd0
  have h0 : (0 : M) ∈ MulAction.fixedPoints H M := fun h => by
    show (h : (M →ₗ[k] M)ˣ) • (0 : M) = 0
    exact smul_zero _
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hcard h0
  exact ⟨b, hb0.symm, fun g hg => hb ⟨_, g, hg, rfl⟩⟩

end Groups

end GroundTheory.ProfCoh
