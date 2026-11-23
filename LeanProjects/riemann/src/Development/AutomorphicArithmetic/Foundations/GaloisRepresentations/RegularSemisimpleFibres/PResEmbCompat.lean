import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pow_self_of_alg (k : Type) [Field k] [Finite k] (x : AlgebraicClosure k) :
    ∃ c : ℕ, 2 ≤ c ∧ x ^ c = x := by
  have hx : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional k (IntermediateField.adjoin k {x}) := IntermediateField.adjoin.finiteDimensional hx
  haveI : Finite (IntermediateField.adjoin k {x}) := Module.finite_of_finite k
  haveI : Fintype (IntermediateField.adjoin k {x}) := Fintype.ofFinite _
  refine ⟨Fintype.card (IntermediateField.adjoin k {x}), Fintype.one_lt_card, ?_⟩
  have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : IntermediateField.adjoin k {x})
  exact congrArg Subtype.val h

private theorem exists_preimage {F F' R : Type} [Field F] [Field F'] [IsAlgClosed F'] [Field R]
    (e : F →+* R) (e' : F' →+* R) (h : ∀ x : F, ∃ c : ℕ, 2 ≤ c ∧ x ^ c = x) (x : F) :
    ∃ y, e' y = e x := by
  obtain ⟨c, hc, hx⟩ := h x
  have hmon : (X ^ c - X : Polynomial F').Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (by omega : 1 < c)
  have hroots := hmon.roots_map_of_card_eq_natDegree e' IsAlgClosed.card_roots_eq_natDegree
  have hmem : e x ∈ ((X ^ c - X : Polynomial F').map e').roots := by
    rw [mem_roots (map_monic_ne_zero hmon)]
    simp only [IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, eval_sub, eval_pow, eval_X]
    rw [← map_pow, hx, sub_self]
  rw [← hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

private theorem exists_equiv_of_fin {k k' R : Type} [Field k] [Field k'] [Finite k] [Finite k'] [Field R]
    (e : AlgebraicClosure k →+* R) (e' : AlgebraicClosure k' →+* R) :
    ∃ j : AlgebraicClosure k ≃+* AlgebraicClosure k', ∀ x, e' (j x) = e x := by
  have h1 : ∀ x, ∃ y, e' y = e x := fun x => exists_preimage e e' (pow_self_of_alg k) x
  have h2 : ∀ x, ∃ y, e y = e' x := fun x => exists_preimage e' e (pow_self_of_alg k') x
  have hr : e.range = e'.range := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h1 x
      exact ⟨y, hy⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h2 x
      exact ⟨y, hy⟩
  let φ := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b hab => e.injective (congrArg Subtype.val hab), e.rangeRestrict_surjective⟩
  let ψ := RingEquiv.ofBijective e'.rangeRestrict
    ⟨fun a b hab => e'.injective (congrArg Subtype.val hab), e'.rangeRestrict_surjective⟩
  refine ⟨φ.trans ((RingEquiv.subringCongr hr).trans ψ.symm), fun x => ?_⟩
  have hq := ψ.apply_symm_apply ((RingEquiv.subringCongr hr) (φ x))
  exact congrArg Subtype.val hq

private theorem val_le_one_iff {k : Type} [Field k] [ValuativeRel k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation k Γ) (hu : (valuation k).IsEquiv u) (x : k) : x ∈ 𝒪[k] ↔ u x ≤ 1 := hu.le_one_iff_le_one

private theorem isUnit_iff_val {k : Type} [Field k] [ValuativeRel k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation k Γ) (hu : (valuation k).IsEquiv u) (x : 𝒪[k]) : IsUnit x ↔ u (x : k) = 1 := by
  exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.trans hu.eq_one_iff_eq_one

theorem UpperTheory.Gal.InertialTypesAlt.resEmbCompat :
    ResEmbCompat := by
  intro K M Ω _ _ _ _ _ _ _ _ _ A v w e e' he he'
  obtain ⟨j, hj⟩ := exists_equiv_of_fin e e'
  have eqv : (valuation (v.adicCompletion K)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have eqw : (valuation (w.1.adicCompletion M)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 K)).ne'
  let f : 𝒪[v.adicCompletion K] →+* 𝒪[w.1.adicCompletion M] :=
    (completionMap v w.1).comp (algebraMap 𝒪[v.adicCompletion K] (v.adicCompletion K)) |>.codRestrict
      (𝒪[w.1.adicCompletion M]) (fun x => by
        refine (val_le_one_iff _ eqw _).2 ?_
        change Valued.v (completionMap v w.1 x) ≤ 1
        rw [valued_completionMap]
        exact pow_le_one' ((val_le_one_iff _ eqv _).1 x.2) _)
  have hf : ∀ x, ((f x : 𝒪[w.1.adicCompletion M]) : w.1.adicCompletion M) = completionMap v w.1 x := fun _ => rfl
  haveI : IsLocalHom f := ⟨fun a ha => by
    rw [isUnit_iff_val _ eqw, hf, valued_completionMap] at ha
    rw [isUnit_iff_val _ eqv]
    exact (pow_eq_one_iff.1 ha).resolve_right he0⟩
  refine ⟨IsLocalRing.ResidueField.map f, j, fun x y hy => ?_, fun x => ?_, hj⟩
  · rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    exact Subtype.ext hy
  · obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    have hy1 : Valued.v (y : v.adicCompletion K) ≤ 1 := (val_le_one_iff _ eqv _).1 y.2
    obtain ⟨a, ha⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v (y : v.adicCompletion K) hy1
    have hb1 : Valued.v (algebraMap K (v.adicCompletion K) (a : K)) ≤ 1 := by
      have e2 : algebraMap K (v.adicCompletion K) (a : K) =
          (y : v.adicCompletion K) - ((y : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (a : K)) := by ring
      rw [e2]
      exact (Valuation.map_sub _ _ _).trans (max_le hy1 ha.le)
    let b : 𝒪[v.adicCompletion K] := ⟨algebraMap K _ (a : K), (val_le_one_iff _ eqv _).2 hb1⟩
    have hyb : IsLocalRing.residue _ y = IsLocalRing.residue _ b := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_iff_val _ eqv]
      exact ha.ne
    let a' : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) a
    have ha' : (a' : M) = algebraMap K M (a : K) := rfl
    let z : A := ⟨algebraMap K Ω (a : K), mem_of_isIntegral_int A
      ((RingOfIntegers.isIntegral_coe a).map (IsScalarTower.toAlgHom ℤ K Ω))⟩
    have h1 := he a b z rfl rfl
    have h2 := he' a' (f b) z (by
      rw [hf, ha']
      change completionMap v w.1 (algebraMap K _ (a : K)) = _
      rw [completionMap_algebraMap]
      exact IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M) _) (by
      rw [ha', ← IsScalarTower.algebraMap_apply])
    apply e'.injective
    rw [hj, hyb, h1, IsLocalRing.ResidueField.map_residue, h2]
