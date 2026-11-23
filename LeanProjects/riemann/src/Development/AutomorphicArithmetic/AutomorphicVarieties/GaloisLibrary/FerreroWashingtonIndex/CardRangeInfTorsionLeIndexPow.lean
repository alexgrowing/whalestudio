import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.NilCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors

open UpperTheory.V.FW

private theorem UpperTheory.V.FW.card_range_inf_torsion_le_index_pow (l : ℕ) [Fact l.Prime] (C : Type) [CommGroup C] [Finite C]
    (φ ψ : C →* C) (N : ℕ) (hc : ∀ x, φ (ψ x) = ψ (φ x))
    (hN : ∀ x, ∃ y, (φ y) ^ l = φ (ψ^[N] x)) :
    Nat.card (φ.range ⊓ torK C l : Subgroup C) ≤ (powR C l ⊔ ψ.range).index ^ N := by
  set U : Subgroup C := (powR φ.range l).comap φ.rangeRestrict with hUdef
  have hU : ∀ x, x ∈ U ↔ ∃ y, (φ y) ^ l = φ x := by
    intro x
    constructor
    · rintro ⟨⟨_, y, rfl⟩, hy⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨φ y, y, rfl⟩, Subtype.ext hy⟩
  have h1 : Nat.card (φ.range ⊓ torK C l : Subgroup C) = U.index := by
    rw [hUdef, Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective,
      (cardTors φ.range).1 l]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩,
      fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hle : U ≤ U.comap ψ := by
    intro x hx
    obtain ⟨y, hy⟩ := (hU x).1 hx
    exact (hU _).2 ⟨ψ y, by rw [hc, hc, ← hy, map_pow]⟩
  set S : C ⧸ U →* C ⧸ U := QuotientGroup.map U U ψ hle with hS
  let T : AddMonoid.End (Additive (C ⧸ U)) := MonoidHom.toAdditive S
  have hT : ∀ n (x : C), (T ^ n) (Additive.ofMul (x : C ⧸ U)) =
      Additive.ofMul ((ψ^[n] x : C) : C ⧸ U) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Function.iterate_succ_apply, ← ih]
      rfl
  have hT0 : T ^ N = 0 := by
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have : v = Additive.ofMul (x : C ⧸ U) := by rw [hx]; rfl
    subst this
    have h := hT N x
    rw [(QuotientGroup.eq_one_iff _).2 ((hU _).2 (hN x))] at h
    exact h
  have h2 := nilCard _ T N hT0
  have h3 : (AddMonoidHom.range T).index = S.range.index := rfl
  have h4 : S.range.index ∣ (powR C l ⊔ ψ.range).index := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]
    refine Subgroup.index_dvd_of_le (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      refine ⟨1, ?_⟩
      rw [map_one]
      exact ((QuotientGroup.eq_one_iff _).2 ((hU _).2 ⟨x, by simp⟩)).symm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : C ⧸ U), rfl⟩
  rw [h1]
  refine le_trans (le_of_eq ?_) (h2.trans ?_)
  · rfl
  · rw [h3]
    exact Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h4) N

theorem UpperTheory.V.FW.core :
    ∀ (l : ℕ) [Fact l.Prime] (G C : Type) [CommGroup G] [CommGroup C] [Finite C] (ρ : Representation ℤ G (Additive C)) (J γ : G) (Jc γc : C →* C) (θ : MonoidAlgebra ℤ G) (N : ℕ), J * J = 1 → (∀ x, ρ J (Additive.ofMul x) = Additive.ofMul (Jc x)) → (∀ x, ρ γ (Additive.ofMul x) = Additive.ofMul (γc x)) → ρ.asAlgebraHom (θ * (1 - MonoidAlgebra.of ℤ G J)) = 0 → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} → Nat.card (difR Jc ⊓ torK C l : Subgroup C) ≤ (powR C l ⊔ difR γc).index ^ N := by
  intro l _ G C _ _ _ ρ J γ Jc γc θ N hJJ hJ hγ hθ hmem
  have key : ∀ (g : G) (gc : C →* C), (∀ x, ρ g (Additive.ofMul x) = Additive.ofMul (gc x)) →
      ∀ x, ρ.asAlgebraHom (1 - MonoidAlgebra.of ℤ G g) (Additive.ofMul x) =
        Additive.ofMul ((MonoidHom.id C / gc) x) := by
    intro g gc h x
    rw [map_sub, map_one, Representation.asAlgebraHom_of, LinearMap.sub_apply, h]
    simp
  have hφ := key J Jc hJ
  have hψ := key γ γc hγ
  set φ := MonoidHom.id C / Jc
  set ψ := MonoidHom.id C / γc
  set a := 1 - MonoidAlgebra.of ℤ G J with ha
  set b := 1 - MonoidAlgebra.of ℤ G γ with hb
  have hit : ∀ n x, ρ.asAlgebraHom (b ^ n) (Additive.ofMul x) = Additive.ofMul (ψ^[n] x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, map_mul, Module.End.mul_apply, hψ, ih, Function.iterate_succ_apply]
  refine card_range_inf_torsion_le_index_pow l C φ ψ N (fun x => ?_) (fun x => ?_)
  · apply Additive.ofMul.injective
    rw [← hφ, ← hψ, ← hψ, ← hφ, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul, mul_comm]
  · have hmem' : b ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} := by
      have : b = -(MonoidAlgebra.of ℤ G γ - 1) := by rw [hb, neg_sub]
      rw [this, neg_pow]
      exact Ideal.mul_mem_left _ _ hmem
    obtain ⟨u, w, hw, h1⟩ := Ideal.mem_span_insert.1 hmem'
    obtain ⟨v, z, h2⟩ := Ideal.mem_span_pair.1 hw
    have hJ2 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by
      rw [← map_mul, hJJ, map_one]
    have h3 : a * b ^ N = u * (θ * a) + l • (a * z) := by
      rw [h1, ← h2, ha, nsmul_eq_mul]
      linear_combination (-v) * hJ2
    refine ⟨Additive.toMul (ρ.asAlgebraHom z (Additive.ofMul x)), ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_pow, ← hφ, ← hφ, ← hit, ofMul_toMul, ← Module.End.mul_apply, ← Module.End.mul_apply,
      ← map_mul, ← map_mul, h3, map_add, map_mul _ u, hθ, mul_zero, zero_add, map_nsmul,
      LinearMap.smul_apply]
