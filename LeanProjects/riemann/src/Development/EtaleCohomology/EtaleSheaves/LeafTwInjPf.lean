import Development.EtaleCohomology.EtaleSheaves.LeafTwSecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwInjPf

theorem prim_field {q : ℕ} [NeZero q] {A : Type} [CommRing A] {K : Type} [Field K] (π : A →+* K)
    (ξ : Prim q A) : IsPrimitiveRoot (π ξ.1) q := by
  have hq : (q : K) ≠ 0 := by simpa using (ξ.2.1.map π).ne_zero
  haveI : NeZero (q : K) := ⟨hq⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := Polynomial.aeval_algHom_apply π.toIntAlgHom ξ.1 (Polynomial.cyclotomic q ℤ)
  rw [ξ.2.2, map_zero] at h
  rw [Polynomial.IsRoot, ← Polynomial.map_cyclotomic q (Int.castRingHom K), Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem pow_val_eq {q : ℕ} [NeZero q] {K : Type} [Field K] {μ : K} (hμ : IsPrimitiveRoot μ q) (m n : ℕ) :
    μ ^ m = μ ^ n ↔ (m : ZMod q) = n := by
  have hf : IsOfFinOrder μ := isOfFinOrder_iff_pow_eq_one.2 ⟨q, NeZero.pos q, hμ.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← hμ.eq_orderOf, ZMod.natCast_eq_natCast_iff]

theorem key {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (c : ULift.{1} (ZMod q))
    (h : c • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = 0) :
    c = 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have hμ := prim_field π ζ
  have hex : ∀ ξ : Prim q A, ∃ u : (ZMod q)ˣ, π ξ.1 = π ζ.1 ^ (u : ZMod q).val := by
    intro ξ
    obtain ⟨j, hj, hj'⟩ := hμ.eq_pow_of_pow_eq_one (prim_field π ξ).pow_eq_one
    have cop : j.Coprime q := (hμ.pow_iff_coprime (NeZero.pos q) j).1 (hj' ▸ prim_field π ξ)
    refine ⟨ZMod.unitOfCoprime j cop, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj, hj']
  have uniq : ∀ u w : (ZMod q)ˣ, π ζ.1 ^ (u : ZMod q).val = π ζ.1 ^ (w : ZMod q).val → u = w := by
    intro u w huw
    rw [pow_val_eq hμ, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at huw
    exact Units.ext huw
  choose e he using hex
  have hmul : ∀ (ζ' ξ : Prim q A) (b : (ZMod q)ˣ), ξ.1 = ζ'.1 ^ (b : ZMod q).val → e ξ = e ζ' * b := by
    intro ζ' ξ b hb
    apply uniq
    rw [← he ξ, hb, map_pow, he ζ', ← pow_mul, pow_val_eq hμ]
    push_cast
    simp [ZMod.natCast_zmod_val]
  have h1 : e ζ = 1 := by
    apply uniq
    rw [← he ζ]
    conv_lhs => rw [← pow_one (π ζ.1)]
    rw [pow_val_eq hμ]
    simp [ZMod.natCast_zmod_val]
  let f := Finsupp.linearCombination (ULift.{1} (ZMod q))
    (fun ξ : Prim q A => (ULift.up (((e ξ) ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)))
  have hker : twRel q i A ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, f, Finsupp.linearCombination_single,
      hmul ζ' ξ b hb, mul_zpow, sub_eq_zero]
    apply ULift.ext
    simp [mul_comm]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  have h2 := hker h
  rw [LinearMap.mem_ker, map_smul] at h2
  have h3 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) = 1 := rfl
  simpa [f, Finsupp.linearCombination_single, h1, h3] using h2

theorem aux {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (x y : ULift.{1} (ZMod q))
    (h : x • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) =
      y • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) : x = y :=
  sub_eq_zero.1 (key i ζ (x - y) (by rw [sub_smul, sub_eq_zero]; exact h))

theorem LeafTwInj_of : LeafTwInj := by
  intro q _ B _ ζ k
  refine ⟨fun {X} x y h => ?_⟩
  by_cases hX : Nonempty X.unop.left
  · haveI : Nontrivial Γ(X.unop.left, ⊤) := by
      obtain ⟨p⟩ := hX
      exact RingHom.domain_nontrivial (X.unop.left.presheaf.germ ⊤ p trivial).hom
    have h0 : x • gen ζ k X.unop = y • gen ζ k X.unop := h
    have hxy : x = y := aux (A := Γ(X.unop.left, ⊤)) k _ x y h0
    subst hxy
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact GrothendieckTopology.top_mem _ _
  · haveI : IsEmpty X.unop.left := not_nonempty_iff.1 hX
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ bot_le ?_
    first
      | exact Scheme.bot_mem_grothendieckTopology _
      | exact bot_mem_grothendieckTopology _
      | exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology (P := @Etale) _

end LateralTheory.E.LeafTwInjPf
