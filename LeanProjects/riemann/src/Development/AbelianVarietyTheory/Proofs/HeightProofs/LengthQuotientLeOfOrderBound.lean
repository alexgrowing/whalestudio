import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsIntegralIffMemSpanOneTmulIntegralClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FlatLength
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemIntegralClosureOfMemSpan

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem mem_span_one_tmul_of_order_bound (R R' F F' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F']
    [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')))
    (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Algebra R L] [IsScalarTower R F L] (n : AddValuation L (WithTop ℤ) → ℤ) (η : L) (hη0 : η ≠ 0)
    (hη : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R L, w η = ((n w : ℤ) : WithTop ℤ))
    (x : F' ⊗[F] L)
    (hx : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R L,
      ∀ u : AddValuation (F' ⊗[F] L) (WithTop ℤ), (∀ g : L, u ((1 : F') ⊗ₜ[F] g) = w g) →
        (∀ r : R', 0 ≤ u (algebraMap R' F' r ⊗ₜ[F] (1 : L))) →
          0 ≤ u x + ((n w : ℤ) : WithTop ℤ)) :
    x ∈ Submodule.span R' ((fun l : L => (1 : F') ⊗ₜ[F] l) ''
      {l | ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R L, 0 ≤ w l + ((n w : ℤ) : WithTop ℤ)}) := by
  have hB := isIntegral_iff_mem_span_one_tmul_integralClosure R R' F F' hmax hres L
  obtain ⟨w', h1, h2, -, -⟩ := exists_unique_place_baseChange R R' F F' hmax hres L hB
  have hint : IsIntegral R' (x * (1 : F') ⊗ₜ[F] η) := by
    rw [h2]
    intro w
    rw [AddValuation.map_mul, h1, hη w.1 w.2]
    refine hx w.1 w.2 (w' w) (h1 w) fun r => ?_
    exact (h2 _).1 (isIntegral_algebraMap (R := R') (A := F' ⊗[F] L) (x := r)) w
  have hmem := (hB _).1 hint
  haveI := integralClosure.isDedekindDomain R F L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F L
  have hxe : x = (x * (1 : F') ⊗ₜ[F] η) * (1 : F') ⊗ₜ[F] η⁻¹ := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hη0,
      ← Algebra.TensorProduct.one_def, mul_one]
  rw [hxe]
  generalize x * (1 : F') ⊗ₜ[F] η = y at hmem
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    refine Submodule.subset_span ⟨b * η⁻¹, fun w hw => ?_, ?_⟩
    · rw [← hη w hw, ← AddValuation.map_mul, inv_mul_cancel_right₀ hη0]
      exact (ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.mem_integralClosure_iff R F b).1 hb w hw
    · simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

theorem length_subquot_le_of_injective {A M V : Type} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup V] [Module A V] (Φ : M →ₗ[A] V) (hΦ : Function.Injective Φ)
    (M₀ T : Submodule A M) (N B : Submodule A V) (hN : ∀ a ∈ M₀, Φ a ∈ N) (hB : T.map Φ = B) :
    Module.length A (↥M₀ ⧸ T.comap M₀.subtype) ≤ Module.length A (↥N ⧸ B.comap N.subtype) := by
  have hc : T.comap M₀.subtype = (B.comap N.subtype).comap (Φ.restrict hN) := by
    ext a
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply, ← hB]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, h⟩ => hΦ h ▸ hy⟩
  refine Module.length_le_of_injective
    (Submodule.mapQ _ (B.comap N.subtype) (Φ.restrict hN) hc.le) ?_
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, ← hc, Submodule.mkQ_map_self]

theorem length_quotient_le_of_order_bound :
    ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Fintype ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ), (∀ c, ∃ η : L c, η ≠ 0 ∧ ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R (L c), w η = ((n c w : ℤ) : WithTop ℤ)) → ∀ (δ δ' : Type) (e : δ ≃ δ') (b : δ → ∀ c, L c) (M : Type) [AddCommGroup M] [Module R' M] (M₀ : Submodule R' M) (t : δ' → M) (Ψ : M →ₗ[R'] ∀ c, F' ⊗[F] L c), Function.Injective Ψ → (∀ k c, Ψ (t (e k)) c = (1 : F') ⊗ₜ[F] b k c) → (∀ a ∈ M₀, ∀ c, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R (L c), ∀ u : AddValuation (F' ⊗[F] L c) (WithTop ℤ), (∀ g : L c, u ((1 : F') ⊗ₜ[F] g) = w g) → (∀ r : R', 0 ≤ u (algebraMap R' F' r ⊗ₜ[F] (1 : L c))) → 0 ≤ u (Ψ a c) + ((n c w : ℤ) : WithTop ℤ)) → ∀ S : Set (∀ c, L c), (∀ y : ∀ c, L c, (∀ c, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R (L c), 0 ≤ w (y c) + ((n c w : ℤ) : WithTop ℤ)) → y ∈ S) → Module.length R' (↥M₀ ⧸ (Submodule.span R' (Set.range t)).comap M₀.subtype) ≤ Module.length R (↥(Submodule.span R S) ⧸ (Submodule.span R (Set.range b)).comap (Submodule.span R S).subtype) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres ι _ L _ _ _ _ _ _ n hη δ δ' e b
    M _ _ M₀ t Ψ hΨ ht hM₀ S hS
  classical
  let E : (F' ⊗[F] (∀ c, L c)) ≃ₗ[R'] (∀ c, F' ⊗[F] L c) :=
    (TensorProduct.piRight F F' F' L).restrictScalars R'
  have hE : ∀ v : ∀ c, L c, E ((1 : F') ⊗ₜ[F] v) = fun c => (1 : F') ⊗ₜ[F] v c := fun v => rfl
  have hspan : ∀ X : Set (∀ c, L c),
      Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) '' (Submodule.span R X : Set _))
        = Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) '' X) := by
    intro X
    refine le_antisymm (Submodule.span_le.2 ?_)
      (Submodule.span_mono (Set.image_mono Submodule.subset_span))
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span ⟨v, hv, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [TensorProduct.tmul_add]
      exact Submodule.add_mem _ ha hb
    | smul r v _ hv =>
      have : (1 : F') ⊗ₜ[F] (r • v) = algebraMap R R' r • ((1 : F') ⊗ₜ[F] v) := by
        rw [TensorProduct.smul_tmul', ← IsScalarTower.algebraMap_smul F r v,
          ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      simp only [this]
      exact Submodule.smul_mem _ _ hv
  refine le_trans (length_subquot_le_of_injective (E.symm.toLinearMap ∘ₗ Ψ)
    (E.symm.injective.comp hΨ) M₀ _
    (Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) '' (Submodule.span R S : Set _)))
    (Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) ''
      (Submodule.span R (Set.range b) : Set _))) ?_ ?_) (le_of_eq ?_)
  · intro a ha
    rw [hspan, LinearMap.comp_apply, ← Finset.univ_sum_single (Ψ a), map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨η, hη0, hη⟩ := hη c
    have hx := mem_span_one_tmul_of_order_bound R R' F F' hmax hres (L c) (n c) η hη0 hη
      (Ψ a c) (hM₀ a ha c)
    generalize Ψ a c = x at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨Pi.single c l, hS _ fun c' w hw => ?_, ?_⟩
      · rcases eq_or_ne c' c with rfl | hc
        · rw [Pi.single_eq_same]; exact hl w hw
        · rw [Pi.single_eq_of_ne hc, AddValuation.map_zero, top_add]; exact le_top
      · refine (LinearEquiv.eq_symm_apply E).2 ?_
        rw [hE]
        funext c'
        rcases eq_or_ne c' c with rfl | hc
        · simp only [Pi.single_eq_same]
        · simp only [Pi.single_eq_of_ne hc, TensorProduct.tmul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · rw [hspan, Submodule.map_span, ← Set.range_comp, ← Set.range_comp,
      ← e.surjective.range_comp]
    congr 2
    funext k
    refine (LinearEquiv.symm_apply_eq E).2 ?_
    funext c
    exact ht k c
  · exact (spanBaseChangeSubquotEquiv F R' F' (Submodule.span R S)
      (Submodule.span R (Set.range b))).length_eq.symm.trans
      (ReciprocityTheory.ChartRestriction.G.T0.length_baseChange_eq hmax _)

end GlobalTheory
