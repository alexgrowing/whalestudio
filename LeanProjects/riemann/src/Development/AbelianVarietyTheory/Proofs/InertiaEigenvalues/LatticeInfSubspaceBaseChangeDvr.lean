import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.LatticeInterBaseChange

end GlobalTheory.LatticeInterBaseChange

namespace GlobalTheory.LatticeInterBaseChange

end GlobalTheory.LatticeInterBaseChange

namespace GlobalTheory.LatticeInterBaseChange

open NumberField IsDedekindDomain Module in
private theorem exists_functional_comp_eq {K F : Type} [Field K] [Field F] (e : K →+* F)
    {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module F V']
    (iV : V →ₛₗ[e] V') {ι : Type} (b : Basis ι K V)
    (hli : LinearIndependent F (fun a => iV (b a))) (φ : V →ₗ[K] K) :
    ∃ ψ : V' →ₗ[F] F, ∀ v, ψ (iV v) = e (φ v) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).constr F (fun a => e (φ (b a))))
  let f₁ : V →ₛₗ[e] F := g.comp iV
  let f₂ : V →ₛₗ[e] F :=
    { toFun := fun v => e (φ v)
      map_add' := fun v w => by simp
      map_smul' := fun t v => by simp }
  have hf : f₁ = f₂ := by
    refine b.ext fun a => ?_
    have h := LinearMap.congr_fun hg (Basis.span hli a)
    rw [Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Basis.span_apply] at h
    exact h
  exact ⟨g, fun v => LinearMap.congr_fun hf v⟩

open NumberField IsDedekindDomain Module in
private theorem exists_integral_inverse_coefficients {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : Fin n → K) :
    ∃ β : Fin n → K, (∀ j k, ∃ r : 𝓞 K, (r : K) = β j * c k) ∧
      ∀ k, c k * ∑ j, β j * c j = c k := by
  classical
  by_cases hc : ∀ k, c k = 0
  · exact ⟨0, fun j k => ⟨0, by simp⟩, fun k => by simp [hc k]⟩
  push_neg at hc
  obtain ⟨k₀, hk₀⟩ := hc
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanFinset (𝓞 K) Finset.univ c
  have hIc : (I : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) (Set.range c) := by
    change Submodule.span (𝓞 K) (c '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) = _
    rw [Finset.coe_univ, Set.image_univ]
  have hI : I ≠ 0 := by
    intro h
    exact hk₀ ((FractionalIdeal.spanFinset_eq_zero.1 h) k₀ (Finset.mem_univ _))
  have h1 : (1 : K) ∈ (I : Submodule (𝓞 K) K) *
      ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key : ∃ β : Fin n → K,
      (∀ j, β j ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) ∧
        (1 : K) = ∑ j, β j * c j := by
    refine Submodule.mul_induction_on (C := fun z => ∃ β : Fin n → K,
      (∀ j, β j ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) ∧
        z = ∑ j, β j * c j) h1 ?_ ?_
    · intro m hm y hy
      rw [hIc, Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨r, rfl⟩ := hm
      refine ⟨fun j => r j • y, fun j => Submodule.smul_mem _ (r j) hy, ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Algebra.smul_def]
      ring
    · rintro x y ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
      exact ⟨β + β', fun j => add_mem (hβ j) (hβ' j),
        by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
  obtain ⟨β, hβI, hβ1⟩ := key
  refine ⟨β, fun j k => ?_, fun k => by rw [← hβ1, mul_one]⟩
  have hck : c k ∈ I := by
    rw [← FractionalIdeal.mem_coe, hIc]
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
    ((FractionalIdeal.mem_inv_iff hI).1 (FractionalIdeal.mem_coe.1 (hβI j)) (c k) hck)
  exact ⟨r, hr⟩

open NumberField IsDedekindDomain Module in
private theorem mem_span_image_inf_ker {K F R : Type} [Field K] [NumberField K] [Field F]
    [CommRing R] [Algebra R F] (e : K →+* F) {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module F V'] [Module R V']
    [IsScalarTower R F V'] (iV : V →ₛₗ[e] V')
    (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap R F).range) (φ : V →ₗ[K] K) (ψ : V' →ₗ[F] F)
    (hψ : ∀ v, ψ (iV v) = e (φ v)) (A : Submodule (𝓞 K) V) {x : V'}
    (hx : x ∈ Submodule.span R (iV '' (A : Set V))) (h0 : ψ x = 0) :
    x ∈ Submodule.span R
      (iV '' ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) := by
  obtain ⟨n, r, g, hxg⟩ := Submodule.mem_span_set'.1 hx
  choose a ha hag using fun i => (g i).2
  obtain ⟨β, hβint, hβ⟩ := exists_integral_inverse_coefficients (fun i => φ (a i))
  choose ρ hρ using hβint
  beta_reduce at hρ hβ
  have hρs : ∀ j k, (ρ j k) • a j = (β j * φ (a k)) • a j := by
    intro j k
    rw [← hρ j k, ← algebraMap_smul K (ρ j k) (a j)]
  let w : Fin n → V := fun k => a k - ∑ j, (ρ j k) • a j
  have hwA : ∀ k, w k ∈ A := fun k =>
    sub_mem (ha k) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (ha j))
  have hwφ : ∀ k, φ (w k) = 0 := by
    intro k
    have h := hβ k
    rw [Finset.mul_sum] at h
    simp only [w, map_sub, map_sum, hρs, map_smul, smul_eq_mul]
    rw [sub_eq_zero]
    conv_lhs => rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∑ k, algebraMap R F (r k) * e (φ (a k)) = 0 := by
    rw [← h0, ← hxg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hag k, ← algebraMap_smul F (r k) (iV (a k)), LinearMap.map_smul, smul_eq_mul, hψ]
  have hiw : ∀ k, iV (w k) = iV (a k) - ∑ j, (e (β j) * e (φ (a k))) • iV (a j) := by
    intro k
    simp only [w, map_sub, map_sum, hρs, LinearMap.map_smulₛₗ, map_mul]
  have hx' : x = ∑ k, r k • iV (w k) := by
    simp only [hiw, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
    have h2 : ∑ k, ∑ j, r k • (e (β j) * e (φ (a k))) • iV (a j) = 0 := by
      have h3 : ∀ k j, r k • (e (β j) * e (φ (a k))) • iV (a j) =
          (e (β j) * (algebraMap R F (r k) * e (φ (a k)))) • iV (a j) := by
        intro k j
        rw [← algebraMap_smul F (r k), smul_smul]
        congr 1
        ring
      simp only [h3]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_smul, ← Finset.mul_sum, key, mul_zero, zero_smul]
    rw [h2, sub_zero, ← hxg]
    exact Finset.sum_congr rfl fun k _ => by rw [hag k]
  rw [hx']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨w k, Submodule.mem_inf.2 ⟨hwA k, LinearMap.mem_ker.2 (hwφ k)⟩, rfl⟩)

open NumberField IsDedekindDomain Module in

theorem _root_.GlobalTheory.LatticeInterBaseChange.span_inf_baseChange : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (A : Submodule (𝓞 K) V) (U : Submodule K V), Submodule.span O (iV '' ((A ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) = Submodule.span O (iV '' (A : Set V)) ⊓ (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O := by
  intro K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he A U
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨v, (Submodule.mem_inf.1 hv).1, rfl⟩,
      Submodule.subset_span ⟨v, (Submodule.mem_inf.1 hv).2, rfl⟩⟩
  · intro x hx
    obtain ⟨hxA, hxU⟩ := Submodule.mem_inf.1 hx
    classical
    let bQ := Module.finBasis K (V ⧸ U)
    let f : Fin (Module.finrank K (V ⧸ U)) → V →ₗ[K] K := fun j => (bQ.coord j).comp U.mkQ
    have hU : ∀ v, v ∈ U ↔ ∀ j, f j v = 0 := by
      intro v
      simp only [f, LinearMap.comp_apply, Basis.coord_apply, Submodule.mkQ_apply]
      constructor
      · intro h j
        rw [(Submodule.Quotient.mk_eq_zero U).2 h, map_zero, Finsupp.zero_apply]
      · intro h
        exact (Submodule.Quotient.mk_eq_zero U).1
          ((LinearEquiv.map_eq_zero_iff bQ.repr).1 (Finsupp.ext h))
    choose ψ hψ using fun j => exists_functional_comp_eq e iV b hli (f j)
    have hψx : ∀ j, ψ j x = 0 := by
      intro j
      have hle : Submodule.span (FractionRing O) (iV '' (U : Set V)) ≤ LinearMap.ker (ψ j) := by
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, hψ, (hU v).1 hv j, map_zero]
      exact hle hxU
    have claim : ∀ s : Finset (Fin (Module.finrank K (V ⧸ U))), ∀ (A' : Submodule (𝓞 K) V) (y : V'),
        y ∈ Submodule.span O (iV '' (A' : Set V)) → (∀ j ∈ s, ψ j y = 0) →
        y ∈ Submodule.span O (iV '' ((A' ⊓ ⨅ j ∈ s, (LinearMap.ker (f j)).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro A' y hy _
        simpa using hy
      | insert j s hj ih =>
        intro A' y hy h0
        have h1 := mem_span_image_inf_ker e iV he (f j) (ψ j) (hψ j) A' hy
          (h0 j (Finset.mem_insert_self j s))
        have h2 := ih _ y h1 fun i hi => h0 i (Finset.mem_insert_of_mem hi)
        refine Submodule.span_mono (Set.image_mono ?_) h2
        intro v hv
        simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, Finset.mem_insert] at hv ⊢
        refine ⟨hv.1.1, fun i hi => ?_⟩
        rcases hi with rfl | hi
        · exact hv.1.2
        · exact hv.2 i hi
    have hfin := claim Finset.univ A x hxA fun j _ => hψx j
    refine Submodule.span_mono (Set.image_mono ?_) hfin
    intro v hv
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf,
      Submodule.restrictScalars_mem, LinearMap.mem_ker, Finset.mem_univ, forall_const] at hv ⊢
    exact ⟨hv.1, (hU v).2 hv.2⟩

end GlobalTheory.LatticeInterBaseChange
