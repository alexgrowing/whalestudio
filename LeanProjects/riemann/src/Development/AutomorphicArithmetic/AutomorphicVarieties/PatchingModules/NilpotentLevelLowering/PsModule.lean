import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem psm_mem_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem psm_prec_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, psm_mem_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, psm_mem_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem psm_prec_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := psm_prec_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem psm_ev {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S) [IsAdicComplete m S]
    (f : R →+* S) (a : σ → S) (ha : ∀ s, a s ∈ m.radical) :
    ∃ F : MvPowerSeries σ R →+* S, (∀ x, F (MvPowerSeries.C x) = f x) ∧ ∀ s, F (MvPowerSeries.X s) = a s := by
  letI : UniformSpace R := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  letI : WithIdeal S := ⟨m⟩
  have hm : IsAdic m := rfl
  obtain ⟨h1, h2⟩ := hm.isAdicComplete_iff.1 inferInstance
  haveI : IsLinearTopology S S := Ideal.isLinearTopology m
  have hf : Continuous f := continuous_of_discreteTopology
  have hE : MvPowerSeries.HasEval a := by
    refine ⟨fun s => ?_, by simp⟩
    rw [IsTopologicallyNilpotent, hm.hasBasis_nhds_zero.tendsto_right_iff]
    intro n _
    obtain ⟨e, he⟩ := ha s
    filter_upwards [Filter.eventually_ge_atTop (e * n)] with k hk
    have h3 := Ideal.pow_mem_pow he n
    rw [← pow_mul] at h3
    exact Ideal.pow_mem_of_pow_mem _ h3 hk
  exact ⟨MvPowerSeries.eval₂Hom hf hE,
    fun x => by rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C],
    fun s => by rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]⟩

private theorem psm_rad {Λ B M : Type} [CommRing Λ] [CommRing B] [Algebra Λ B] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] (I : Ideal Λ) (ι : B →ₐ[Λ] Module.End Λ M) (hι : Function.Injective ι) (b : B)
    (hb : ∀ x : M, ∀ᶠ r : ℕ in Filter.atTop, (ι b ^ r) x ∈ (I • ⊤ : Submodule Λ M)) :
    b ∈ (I.map (algebraMap Λ B)).radical := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  obtain ⟨r, hr⟩ := (Filter.eventually_all.2 fun i => hb (v i)).exists
  have h1 : LinearMap.range (ι b ^ r) ≤ I • ⊤ := by
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_le, hv]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hr i
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul Λ (ι b ^ r) I h1
  rw [← map_pow, Polynomial.aeval_algHom_apply, map_eq_zero_iff _ hι, hp.as_sum, map_add, map_sum,
    add_eq_zero_iff_eq_neg, map_pow, Polynomial.aeval_X, ← pow_mul] at h0
  refine ⟨_, h0 ▸ neg_mem (Ideal.sum_mem _ fun k hk => ?_)⟩
  rw [map_mul, Polynomial.aeval_C]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)) (hc k)

private theorem psm_abs {Λ A B M κ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing A] [CommRing B] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Finite κ] (g : Λ →+* B) (f : A →+* B) (ι : B →+* Module.End Λ M)
    (hι : Function.Injective ι) (hg : ∀ c, ι (g c) = algebraMap Λ _ c) (b : κ → B)
    (hb : topNil (maximalIdeal Λ) (fun i => ι (b i)) = ⊤) :
    ∃ F : MvPowerSeries κ A →+* B, (∀ x, F (MvPowerSeries.C x) = f x) ∧ ∀ s, F (MvPowerSeries.X s) = b s := by
  letI : Algebra Λ B := g.toAlgebra
  let ι' : B →ₐ[Λ] Module.End Λ M := { ι with commutes' := hg }
  haveI : Module.Finite Λ B := Module.Finite.of_injective ι'.toLinearMap hι
  haveI : IsPrecomplete (maximalIdeal Λ) B := psm_prec_finite _
  haveI : IsAdicComplete ((maximalIdeal Λ).map (algebraMap Λ B)) B :=
    { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 inferInstance
      toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 inferInstance }
  refine psm_ev ((maximalIdeal Λ).map (algebraMap Λ B)) f b fun s => psm_rad _ ι' hι _ fun x => ?_
  have h := mem_topNil.1 (hb.ge (Submodule.mem_top (x := x))) s 1
  rwa [pow_one] at h

theorem UpperTheory.V.Pa.Lev.psModule :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (A M κ : Type) [CommRing A] [Algebra Λ A] [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] [Module.Finite Λ M] [Fintype κ] (T : κ → Module.End A M), (∀ i j, Commute (T i) (T j)) → topNil (maximalIdeal Λ) (fun i => (T i).restrictScalars Λ) = ⊤ → ∃ act : MvPowerSeries κ A →ₐ[A] Module.End A M, ∀ i, act (MvPowerSeries.X i) = T i := by
  intro Λ _ _ _ _ A M κ _ _ _ _ _ _ _ _ T hT htop
  let B := Algebra.adjoin A (Set.range T)
  have hcomm : IsMulCommutative B := Algebra.isMulCommutative_adjoin A (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hT i j).eq)
  letI : CommRing B := { (inferInstance : Ring B) with mul_comm := fun x y => hcomm.is_comm.comm x y }
  let ι : B →+* Module.End Λ M :=
    { toFun := fun x => (x : Module.End A M).restrictScalars Λ
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (LinearMap.ext fun m => LinearMap.congr_fun h m)
  obtain ⟨F, hC, hX⟩ := psm_abs (A := A) ((algebraMap A B).comp (algebraMap Λ A)) (algebraMap A B) ι hι
    (fun c => LinearMap.ext fun m => algebraMap_smul A c m)
    (fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩) htop
  refine ⟨{ (B.val : B →+* Module.End A M).comp F with commutes' := fun c => ?_ }, fun i => ?_⟩
  · show ((F (MvPowerSeries.C c) : B) : Module.End A M) = _
    rw [hC]; rfl
  · show ((F (MvPowerSeries.X i) : B) : Module.End A M) = _
    rw [hX]
