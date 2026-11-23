import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvrStatement
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.StabIdx

theorem relIndex_ne_zero_of_map {G X : Type} [Group G] [Finite X] (H K : Subgroup G) (f : K → X)
    (hf : ∀ a b : K, f a = f b → (a : G)⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_injective (fun q : K ⧸ H.subgroupOf K => f q.out) ?_
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hf _ _ h
  exact Subgroup.index_ne_zero_of_finite

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem mem_stabilizer_of {g : A} (L : stLat O E g) (t : Aˣ)
    (h1 : ∀ y ∈ (L : Submodule O A), (t : A) * y ∈ (L : Submodule O A))
    (h2 : ∀ y ∈ (L : Submodule O A), ((t⁻¹ : Aˣ) : A) * y ∈ (L : Submodule O A)) :
    t ∈ MulAction.stabilizer Aˣ L := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  rw [stLat_smul_val]
  ext x
  rw [mem_mulLat_iff]
  constructor
  · intro hx
    have := h1 _ hx
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this
  · intro hx
    exact h2 _ hx

theorem finite_quotient_span [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {c : O} (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    (inferInstance : Finite (IsLocalRing.ResidueField O))
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O)) n
  rwa [hm, Ideal.span_singleton_pow, ← hn] at this

variable [IsDomain O] [Algebra O E] [IsFractionRing O E] [IsScalarTower O E A]

theorem exists_smul_mul_mem (C L : Submodule O A) (hC : C.FG) (hL : IsLat O E L) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ C, ∀ y ∈ L, c • (x * y) ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hC
  obtain ⟨t, ht⟩ := hL.1
  have hex : ∀ p : A × A, ∃ r : O, r ≠ 0 ∧ r • (p.1 * p.2) ∈ L := fun p =>
    ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_smul_mem_of_mem_span (C := E) L (by rw [hL.2]; trivial)
  choose r hr0 hrm using hex
  refine ⟨∏ p ∈ s ×ˢ t, r p, Finset.prod_ne_zero_iff.2 fun p _ => hr0 p, ?_⟩
  have hgen : ∀ a ∈ s, ∀ b ∈ t, (∏ p ∈ s ×ˢ t, r p) • (a * b) ∈ L := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_product.2 ⟨ha, hb⟩ : (a, b) ∈ s ×ˢ t)
    rw [hk, mul_comm, mul_smul]
    exact L.smul_mem _ (hrm (a, b))
  intro x hx y hy
  rw [← ht] at hy
  induction hy using Submodule.span_induction with
  | mem b hb =>
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hgen a ha b hb
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul, smul_add]; exact L.add_mem hu hv
    | smul o u _ hu => rw [smul_mul_assoc, smul_comm]; exact L.smul_mem _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, smul_add]; exact L.add_mem hu hv
  | smul o u _ hu => rw [mul_smul_comm, smul_comm]; exact L.smul_mem _ hu

theorem relIndex_ne_zero_of_fg [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {g : A} (hC : (Subalgebra.toSubmodule (integralClosure O A)).FG) (L : stLat O E g) :
    (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  classical
  set C := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  obtain ⟨c, hc0, hcL⟩ := exists_smul_mul_mem (E := E) C (L : Submodule O A) hC L.2.1
  haveI := finite_quotient_span hc0
  haveI : Finite (C ⧸ (⊤ : Submodule O C)) := by
    haveI : Subsingleton (C ⧸ (⊤ : Submodule O C)) := Submodule.Quotient.subsingleton_iff.2 rfl
    infer_instance
  haveI : Finite (C ⧸ Ideal.span {c} • (⊤ : Submodule O C)) :=
    Submodule.finite_quotient_smul _ ((Submodule.fg_top C).2 hC)
  have hmemC : ∀ x : A, IsIntegral O x → x ∈ C := fun x hx => hx
  let f : intUnits O A → C ⧸ Ideal.span {c} • (⊤ : Submodule O C) := fun t =>
    Submodule.Quotient.mk ⟨((t : Aˣ) : A), hmemC _ t.2.1⟩
  refine relIndex_ne_zero_of_map _ _ f fun a b hab => ?_
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hab
  obtain ⟨n, -, hn⟩ := hab
  have hn' : c • (n : A) = ((a : Aˣ) : A) - ((b : Aˣ) : A) := by
    have := congrArg Subtype.val hn
    simpa using this
  have ha : ((a : Aˣ)⁻¹ : Aˣ).val * (a : Aˣ).val = 1 := Units.inv_mul _
  have hb : ((b : Aˣ)⁻¹ : Aˣ).val * (b : Aˣ).val = 1 := Units.inv_mul _
  have hna : ((a : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (a.2.2.mul n.2)
  have hnb : ((b : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (b.2.2.mul n.2)
  apply mem_stabilizer_of L
  · intro y hy
    have e : (((a : Aˣ)⁻¹ * (b : Aˣ) : Aˣ) : A) * y =
        y - c • ((((a : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (((a : Aˣ)⁻¹ : Aˣ).val * y) * hn' + y * ha
    rw [e]
    exact L.1.sub_mem hy (hcL _ hna _ hy)
  · intro y hy
    have e : ((((a : Aˣ)⁻¹ * (b : Aˣ))⁻¹ : Aˣ) : A) * y =
        y + c • ((((b : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [mul_inv_rev, inv_inv, Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (-(((b : Aˣ)⁻¹ : Aˣ).val * y)) * hn' + y * hb
    rw [e]
    exact L.1.add_mem hy (hcL _ hnb _ hy)

theorem stabilizer_relIndex_intUnits_ne_zero : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A]
    [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable →
    ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hg L
  haveI := GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft E A g hg
  exact relIndex_ne_zero_of_fg (GlobalTheory.T.integralClosure_fg_finiteEtale_dvr O E A) L

end GlobalTheory.UnitLemma.StabIdx
