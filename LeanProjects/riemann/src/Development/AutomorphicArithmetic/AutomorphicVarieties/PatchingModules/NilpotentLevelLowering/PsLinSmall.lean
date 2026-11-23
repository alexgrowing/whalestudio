import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem psLin_span {A κ : Type} [CommRing A] (d : ℕ) (s : Finset κ) :
    ∀ f : MvPowerSeries κ A, (∀ e : κ →₀ ℕ, (∀ i ∈ s, e i < d) → MvPowerSeries.coeff e f = 0) →
      f ∈ Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro f hf
    have h0 : f = 0 := by
      ext e
      simpa using hf e (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  · intro a s _ ih f hf
    let g : MvPowerSeries κ A := fun e => MvPowerSeries.coeff (e + Finsupp.single a d) f
    let r : MvPowerSeries κ A := fun e => if e a < d then MvPowerSeries.coeff e f else 0
    have hfr : f = (MvPowerSeries.X a) ^ d * g + r := by
      ext e
      rw [map_add, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
      by_cases h : e a < d
      · have h' : ¬ (Finsupp.single a d ≤ e) := by
          rw [Finsupp.single_le_iff]
          omega
        rw [if_neg h']
        show _ = 0 + (if e a < d then MvPowerSeries.coeff e f else 0)
        rw [if_pos h, zero_add]
      · have h' : Finsupp.single a d ≤ e := by
          rw [Finsupp.single_le_iff]
          omega
        rw [if_pos h']
        show _ = 1 * MvPowerSeries.coeff (e - Finsupp.single a d + Finsupp.single a d) f +
          (if e a < d then MvPowerSeries.coeff e f else 0)
        rw [if_neg h, tsub_add_cancel_of_le h', one_mul, add_zero]
    rw [hfr]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)) (ih r ?_)
    intro e he
    show (if e a < d then MvPowerSeries.coeff e f else 0) = 0
    split_ifs with h
    · exact hf e (fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h
        · exact he i hi)
    · rfl

private theorem psLin_small {Λ A M κ : Type} [CommRing Λ] [CommRing A] [AddCommGroup M] [Module Λ M]
    (act : MvPowerSeries κ A →+* Module.End Λ M) (I : Ideal Λ) (d : ℕ) (m : M)
    (h : ∀ i, (act (MvPowerSeries.X i) ^ d) m ∈ (I • ⊤ : Submodule Λ M)) (f : MvPowerSeries κ A)
    (hf : f ∈ Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d)) :
    act f m ∈ (I • ⊤ : Submodule Λ M) := by
  have hT : ∀ (T : Module.End Λ M) (y : M), y ∈ (I • ⊤ : Submodule Λ M) →
      T y ∈ (I • ⊤ : Submodule Λ M) :=
    fun T y hy => Submodule.smul_top_le_comap_smul_top I T hy
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [map_pow]
    exact h i
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, map_mul, Module.End.mul_apply]
    exact hT _ _ hx

theorem UpperTheory.V.Pa.Lev.psLin :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (A M M' κ : Type) [CommRing A] [AddCommGroup M] [Module Λ M] [AddCommGroup M'] [Module Λ M'] [Module.Finite Λ M] [Module.Finite Λ M'] [Fintype κ] (act : MvPowerSeries κ A →+* Module.End Λ M) (act' : MvPowerSeries κ A →+* Module.End Λ M') (φ : M →ₗ[Λ] M'), topNil (maximalIdeal Λ) (fun i => act (MvPowerSeries.X i)) = ⊤ → topNil (maximalIdeal Λ) (fun i => act' (MvPowerSeries.X i)) = ⊤ → (∀ a m, φ (act (MvPowerSeries.C a) m) = act' (MvPowerSeries.C a) (φ m)) → (∀ i m, φ (act (MvPowerSeries.X i) m) = act' (MvPowerSeries.X i) (φ m)) → ∀ f m, φ (act f m) = act' f (φ m) := by
  intro Λ _ _ _ _ A M M' κ _ _ _ _ _ _ _ _ act act' φ hN hN' hC hX f m
  classical
  have hpoly : ∀ P : MvPolynomial κ A, ∀ y,
      φ (act (P : MvPowerSeries κ A) y) = act' (P : MvPowerSeries κ A) (φ y) := by
    intro P
    refine MvPolynomial.induction_on
      (motive := fun P => ∀ y, φ (act (P : MvPowerSeries κ A) y) = act' (P : MvPowerSeries κ A) (φ y))
      P ?_ ?_ ?_
    · intro a y
      rw [MvPolynomial.coe_C]
      exact hC a y
    · intro p q hp hq y
      rw [MvPolynomial.coe_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
        hp, hq]
    · intro p i hp y
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hp, hX]
  rw [← sub_eq_zero]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M') (maximalIdeal Λ)
    (IsLocalRing.maximalIdeal.isMaximal Λ).ne_top
  have hmem : φ (act f m) - act' f (φ m) ∈ ⨅ k, (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M') := by
    rw [Submodule.mem_iInf]
    intro k
    have ev1 : ∀ᶠ r in Filter.atTop, ∀ i,
        (act (MvPowerSeries.X i) ^ r) m ∈ (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M) :=
      Filter.eventually_all.mpr fun i =>
        (mem_topNil (I := maximalIdeal Λ) (T := fun i => act (MvPowerSeries.X i)) (m := m)).mp
          (by rw [hN]; exact Submodule.mem_top) i k
    have ev2 : ∀ᶠ r in Filter.atTop, ∀ i,
        (act' (MvPowerSeries.X i) ^ r) (φ m) ∈ (maximalIdeal Λ) ^ k • (⊤ : Submodule Λ M') :=
      Filter.eventually_all.mpr fun i =>
        (mem_topNil (I := maximalIdeal Λ) (T := fun i => act' (MvPowerSeries.X i)) (m := φ m)).mp
          (by rw [hN']; exact Submodule.mem_top) i k
    obtain ⟨d, hd1, hd2, hd0⟩ := (ev1.and (ev2.and (Filter.eventually_ge_atTop 1))).exists
    let n0 : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => d - 1
    let P := MvPowerSeries.trunc' A n0 f
    have hr : f - (P : MvPowerSeries κ A) ∈
        Ideal.span (Set.range fun i : κ => (MvPowerSeries.X i : MvPowerSeries κ A) ^ d) := by
      apply psLin_span d Finset.univ
      intro e he
      have hle : e ≤ n0 := Finsupp.le_def.mpr fun i => by
        have := he i (Finset.mem_univ i)
        show e i ≤ d - 1
        omega
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]
    have h1 := psLin_small act ((maximalIdeal Λ) ^ k) d m hd1 _ hr
    have h2 := psLin_small act' ((maximalIdeal Λ) ^ k) d (φ m) hd2 _ hr
    have h3 := Submodule.smul_top_le_comap_smul_top ((maximalIdeal Λ) ^ k) φ h1
    have hsplit : φ (act f m) - act' f (φ m) =
        φ (act (f - ↑P) m) - act' (f - ↑P) (φ m) := by
      simp only [map_sub, LinearMap.sub_apply, hpoly P m, sub_sub_sub_cancel_right]
    rw [hsplit]
    exact Submodule.sub_mem _ h3 h2
  rw [hbot] at hmem
  exact (Submodule.mem_bot Λ).mp hmem
