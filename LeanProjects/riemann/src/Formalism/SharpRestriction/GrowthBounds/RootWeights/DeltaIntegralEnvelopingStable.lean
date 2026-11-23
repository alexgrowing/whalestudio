import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsIntegralWeightProjections

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def nablaToDeltaMaps (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O (Module.End (KK O) V) where
  carrier := {f | ∀ x ∈ Nabla (O := O) E lam v, f x ∈ Delta (O := O) E v}
  zero_mem' := fun x _ => by simp
  add_mem' := fun {f g} hf hg x hx => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (hf x hx)

theorem nabla_integral_enveloping_stable (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) :
    UZStable (O := O) E (NablaSub (O := O) E lam v) := by
  intro u hu x hx u' hu'
  exact hx (u' * u) (Submonoid.mul_mem _ hu' (Submonoid.subset_closure hu))

theorem delta_integral_enveloping_stable (E : GLOps n (KK O) V) (v : V) : UZStable (O := O) E (Delta (O := O) E v) := by
  intro u hu x hx
  have hle : Delta (O := O) E v ≤ (Delta (O := O) E v).comap (u.restrictScalars O) := by
    unfold Delta
    rw [Submodule.span_le]
    rintro _ ⟨u', hu', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    exact Submodule.subset_span ⟨u * u', Submonoid.mul_mem _ (Submonoid.subset_closure hu) hu', rfl⟩
  exact hle hx

theorem adjoint_divided_power_expansion [CharZero (KK O)] (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) (f : Module.End (KK O) V) :
    divPowE (adjointEndAction E) a b k f =
      ∑ m ∈ range (k + 1), ((-1 : KK O) ^ (k - m)) • (divPowE E a b m * f * divPowE E a b (k - m)) := by
  have hc : Commute (LinearMap.mulLeft (KK O) (E a b)) ((-1 : KK O) • LinearMap.mulRight (KK O) (E a b)) :=
    (LinearMap.commute_mulLeft_right _ _).smul_right _
  have hsub : adjointEndAction E a b =
      LinearMap.mulLeft (KK O) (E a b) + (-1 : KK O) • LinearMap.mulRight (KK O) (E a b) := by
    rw [adjointEndAction, neg_one_smul, sub_eq_add_neg]
  simp only [divPowE]
  rw [hsub, hc.add_pow, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := by simp at hm; omega
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, map_nsmul, map_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← Nat.cast_smul_eq_nsmul (KK O), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Nat.cast_choose (KK O) hmk]
  have h1 : ((m.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (((k - m).factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - m)
  have h3 : ((k.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem nabla_to_delta_maps_stable [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    (lam : Fin n → ℤ) (v : V) : UZStable (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) := by
  intro u hu f hf x hx
  have hN := nabla_integral_enveloping_stable (O := O) E lam v
  have hD := delta_integral_enveloping_stable (O := O) E v
  have htop : ∀ z : V, z ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    intro z
    simp only [iSup_true]
    rw [hE.2.2]
    exact Submodule.mem_top
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · rw [adjoint_divided_power_expansion, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
    have h1 : divPowE E a b (k - m) x ∈ NablaSub (O := O) E lam v := hN _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) x hx
    have h2 : f (divPowE E a b (k - m) x) ∈ Delta (O := O) E v := hf _ h1
    have h3 := hD _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ h2
    have h4 := intCast_smul_mem_submodule (Delta (O := O) E v) ((-1 : ℤ) ^ (k - m)) h3
    simpa using h4
  · have hR : ∀ (m : ℕ) (μ ν : Fin n → ℤ) (z : V), z ∈ weightSp E μ →
        (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) z =
          (∏ j ∈ range m, ((μ a : KK O) - ((ν a : KK O) + j))) • z := by
      intro m μ ν z hz
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          (mem_weightSpace_iff_diag_scalar.1 hz) a, ← sub_smul, map_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]
    have hw : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        (binomE (adjointEndAction E) a k f) y = ∑ ij ∈ antidiagonal k,
          (((Ring.choose (-(ν a)) ij.2 : ℤ) : KK O)) • binomE E a ij.1 (f y) := by
      intro ν y hy
      have hadx : ∀ (g : Module.End (KK O) V) (c : KK O),
          ((adjointEndAction E a a - c • (1 : Module.End (KK O) (Module.End (KK O) V))) g) y =
            (E a a - ((ν a : KK O) + c) • (1 : Module.End (KK O) V)) (g y) := by
        intro g c
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, adjointEndAction_apply,
          Module.End.mul_apply, (mem_weightSpace_iff_diag_scalar.1 hy) a, map_smul, add_smul, LinearMap.add_apply]
        abel
      have hprod : ∀ (m : ℕ) (g : Module.End (KK O) V),
          (((List.range m).map fun j : ℕ => adjointEndAction E a a - (j : KK O) •
            (1 : Module.End (KK O) (Module.End (KK O) V))).prod g) y =
          (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) (g y) := by
        intro m
        induction m with
        | zero => intro g; simp
        | succ m ih =>
          intro g
          rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
            List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton]
          simp only [Module.End.mul_apply]
          rw [ih, hadx]
      obtain ⟨G, h, hh, hfy⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop (f y))
      rw [binomE, LinearMap.smul_apply, LinearMap.smul_apply, hprod, hfy, map_sum, Finset.smul_sum]
      simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμw := (hh μ hμ).2
      rw [hR k μ ν _ hμw, smul_smul]
      simp only [binomial_diagonal_on_weight hμw, map_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      calc ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, ((μ a : KK O) - ((ν a : KK O) + j))
          = ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, (((μ a + -(ν a) : ℤ) : KK O) - (j : KK O)) := by
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            push_cast
            ring
        _ = ((Ring.choose (μ a + -(ν a)) k : ℤ) : KK O) := inv_factorial_prod_eq_choose _ _
        _ = _ := by
            rw [Ring.add_choose_eq k (Commute.all _ _)]
            push_cast
            refine Finset.sum_congr rfl fun ij _ => ?_
            ring
    obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Module.End (KK O) V,
        S = fun j : ℕ => ((((j : ℤ).negOnePow : ℤˣ) : ℤ) : KK O) • shiftedBinomialOperator E a ((j : ℤ) - 1) j := ⟨_, rfl⟩
    have hS : ∀ (j : ℕ) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        S j y = ((Ring.choose (-(ν a)) j : ℤ) : KK O) • y := by
      intro j ν y hy
      rw [hSdef, LinearMap.smul_apply, shifted_binomial_on_weight hy, smul_smul]
      congr 1
      rw [Ring.choose_neg, Units.smul_def, smul_eq_mul, add_sub_assoc]
      push_cast
      ring
    have hop : binomE (adjointEndAction E) a k f = ∑ ij ∈ antidiagonal k, binomE E a ij.1 * f * S ij.2 := by
      apply LinearMap.ext
      intro z
      obtain ⟨F, g, hg, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop z)
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hw ν _ (hg ν hν).2, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hS _ _ _ (hg ν hν).2, map_smul, map_smul]
    rw [hop, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun ij _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have h1 : S ij.2 x ∈ NablaSub (O := O) E lam v := by
      rw [hSdef, LinearMap.smul_apply]
      exact intCast_smul_mem_submodule _ _ (shifted_binomial_preserves_lattice hN a _ _ hx)
    have h2 : f (S ij.2 x) ∈ Delta (O := O) E v := hf _ h1
    exact hD _ (Or.inr ⟨a, ij.1, rfl⟩) _ h2

end hw

end Formalism.MainNotions.G.GLWeightTheory
